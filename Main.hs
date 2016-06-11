{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedLists            #-}
{-# LANGUAGE OverloadedStrings          #-}

import           Control.Applicative
import           Text.Trifecta hiding (source, text)
import           Text.Parser.Token.Highlight
import           Control.Lens hiding (noneOf)
import           Control.Monad.Reader
import           Control.Monad.State
import           Control.Monad.Except
import           Control.Monad.Trans.Either
import           Data.Map.Strict            (Map, fromList)
import           Data.Functor
import           Text.PrettyPrint.ANSI.Leijen ( putDoc, Pretty(..), blue, Doc
                                              , encloseSep, magenta, red, text
                                              , green, yellow)
import           System.IO (hFlush, stdout)

-- | Basic datatypes for Factor
data FItem =
    FInt Integer
  | FBol Bool
  | FIdt String
  | FQut [FItem]
  | FWrd String [FItem]

-- | The state of a factors program as it runs
data FactorState = FactorState
  { _vars  :: Map String [FItem]
  , _stack :: [FItem] }

data FactorError =
  PopEmptyStack |
  TypeError Doc Doc | -- Expected, received
  Unrecognised Doc |
  ParseError

-- | Primitive operations, parameterized over the monad m
-- to allow IO, etc
newtype FactorPrimitives m = FactorPrimitives
  { _primitives :: Map String (m [Doc]) }

makeLenses ''FactorState

makePrisms ''FItem

makeLenses ''FactorPrimitives

showType :: FItem -> Doc
showType (FInt _  ) = green "Integer"
showType (FBol _  ) = green "Bool"
showType (FIdt _  ) = green "Identifier"
showType (FQut _  ) = green "Quote"
showType (FWrd _ _) = green "Word"

instance Pretty FItem where
 pretty (FInt i  ) = blue (pretty i)
 pretty (FBol b  ) = red (pretty b)
 pretty (FIdt s  ) = magenta (text s)
 pretty (FQut q  ) =
   encloseSep (yellow "[ ") (yellow " ]") " " (map pretty q)
 pretty (FWrd n q) =
   encloseSep (yellow ": ") (yellow " ;") " " (magenta (text n) : map pretty q)

instance Pretty FactorError where
  pretty PopEmptyStack = "Tried to pop an empty stack"
  pretty (TypeError e r) = mconcat ["Type error. Expected: ", e, ". Received: ", r]
  pretty (Unrecognised n) = mappend "Unrecognised name: " n
  pretty ParseError = ""

-- | Try pop an item off of the stack, throwing an error on an empty stack
pop :: (MonadError FactorError m, MonadState FactorState m) => m FItem
pop = preuse (stack._Cons) >>= maybe (throwError PopEmptyStack) pop' where
  pop' (x,xs) = do
    stack .= xs
    return x

push :: MonadState FactorState m => FItem -> m ()
push x = stack %= cons x

-- | Run an action without altering the named variables
scoped :: MonadState FactorState m => m a -> m a
scoped f = do
  m <- use vars
  x <- f
  vars .= m
  pure x

-- | Attempt to look up a name, throwing an error if it doesn't exist
getNamed :: ( MonadState FactorState m
            , MonadError FactorError m
            , MonadReader (FactorPrimitives m) m )
         => String -> m [Doc]
getNamed n =
  use (vars . at n) >>=
  maybe (view (primitives . at n) >>=
           maybe (throwError . Unrecognised . pretty . FIdt $ n)
                 scoped)
         eval

lift', sink :: ( MonadError FactorError m
               , MonadState FactorState m )
            => Integer -> m ()
lift' = lift'' . max 1 where
  lift'' 1 = pure ()
  lift'' n = do
    x <- pop
    lift'' (n-1)
    y <- pop
    push x
    push y

sink = sink' . max 1 where
  sink' 1 = pure ()
  sink' n = do
    x <- pop
    y <- pop
    push x
    sink' (n-1)
    push y

fact :: CharParsing m => IdentifierStyle m
fact =
  IdentifierStyle
    "identifier"
    (noneOf "0123456789[]: \t\r\n")
    (noneOf " \t\r\n")
    ["[", "]", ":", "True", "False"]
    Identifier
    ReservedIdentifier

-- | Parser for a single factor item
fItem :: (Monad m, TokenParsing m) => m FItem
fItem = choice
  [ FQut <$> brackets (some fItem) <?> "Quotation"
  , FWrd <$> (colon *> ident fact) <*> (some fItem <* semi) <?> "Word"
  , FBol <$> (reserve fact "True" $> True <|> reserve fact "False" $> False) <?> "Boolean"
  , FInt <$> natural <?> "integer"
  , FIdt <$> ident fact ]

tok :: ( MonadState FactorState m
       , MonadError FactorError m
       , MonadReader (FactorPrimitives m) m)
    => FItem -> m [Doc]
tok (FIdt n) = getNamed n
tok (FWrd n q) = [] <$ (vars . at n ?= q)
tok x = [] <$ push x

eval :: ( MonadState FactorState m
        , MonadError FactorError m
        , MonadReader (FactorPrimitives m) m )
     => [FItem] -> m [Doc]
eval = fmap concat . traverse tok

initPrimitives :: ( MonadError FactorError m
                  , MonadState FactorState m
                  , MonadReader (FactorPrimitives m) m )
               => FactorPrimitives m
initPrimitives = FactorPrimitives (fromList m) where
  m = (".", dot') : map (_2.mapped .~ [])
    [ ("+", intOp (+)), ("-", intOp (-)), ("*", intOp (*))
    , ("/", intOp div) , ("%", intOp mod)
    , ("lift", popInt >>= lift'), ("sink", popInt >>= sink), ("drop", void pop)
    , ("dup", pop >>= (\x -> push x *> push x))
    , ("&&", bolOp (&&)), ("||", bolOp (||))
    , ("if", bool <$> popBool <*> pop <*> pop >>= push)
    , ("==", cmpOp (==)), ("!=", cmpOp (/=)), ("<=", cmpOp (<=))
    , (">=", cmpOp (>=)), ("<", cmpOp (<)), (">", cmpOp (>))
    , ("!", not <$> popBool >>= push . FBol)
    , ("clear", stack .= [])
    , ("freeze", stack %= (pure . FQut))
    , ("empty", FBol <$> uses stack null >>= push)]
  cmpOp o = o <$> popInt <*> popInt >>= push . FBol
  intOp o = o <$> popInt <*> popInt >>= push . FInt
  bolOp o = o <$> popBool <*> popBool >>= push . FBol
  popInt = popType _FInt (green "Integer")
  popBool = popType _FBol (green "Bool")
  popType p d = pop >>= either errs pure . matching p where
    errs = throwError . TypeError d . showType
  bool True  t _ = t
  bool False _ f = f
  dot' = do
    x <- pop
    case x of
      FQut q -> eval q
      r -> pure [pretty r]

parseWithError :: (MonadError FactorError m, MonadIO m) => Parser a -> String -> m a
parseWithError p s = case parseString p mempty s of
  Success x -> pure x
  Failure f -> liftIO (putDoc f) *> throwError ParseError

repl :: ( MonadIO m
        , MonadState FactorState m
        , MonadError FactorError m
        , MonadReader (FactorPrimitives m) m )
     => m ()
repl = forever $ do
  source <- liftIO getLine
  parsed <- parseWithError (many fItem <* eof) source
  result <- eval parsed
  stackt <- use stack
  unless (null stackt) . liftIO $ do
    putStr "Stack : "
    putDoc $ encloseSep "" "" " " (map pretty stackt)
    putChar '\n'
  unless (null result) . liftIO $ do
    putStr "Result: "
    putDoc $ encloseSep "" "" " " result
    putChar '\n'
  liftIO $ hFlush stdout

-- | The Factor monad. This represents the result of evaluating a
-- Factor program.
newtype Factor a = Factor
  { _runFactor :: ReaderT (FactorPrimitives Factor)
                 (StateT FactorState
                 (EitherT FactorError IO))
                  a
  } deriving
    ( Functor, Applicative, Monad, MonadIO
    , MonadError FactorError, MonadState FactorState
    , MonadReader (FactorPrimitives Factor) )

main :: IO ()
main =
  (eitherT (putDoc.pretty) pure .
  flip evalStateT (FactorState mempty []) .
  flip runReaderT initPrimitives .
  _runFactor $ repl) *> putChar '\n'
