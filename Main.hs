{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedLists #-}

import           Control.Applicative
import           Text.Trifecta hiding (source)
import           Text.Parser.Token.Highlight
import           Control.Lens hiding (noneOf)
import           Control.Monad.Reader
import           Control.Monad.State
import           Control.Monad.Except
import           Control.Monad.Trans.Either
import           Data.Map.Strict            (Map, fromList)
import           Data.Functor
import           Text.PrettyPrint.ANSI.Leijen (putDoc)
-- | Basic datatypes for Factor
data FItem =
    FInt Integer
  | FBol Bool
  | FIdt String
  | FQut [FItem]
  | FWrd String [FItem]

data FactorState = FactorState
  { _vars  :: Map String [FItem]
  , _stack :: [FItem] }

data FactorError =
  PopEmptyStack |
  TypeError String String | -- Expected, received
  Unrecognised String |
  ParseError

newtype FactorPrimitives m = FactorPrimitives
  { _primitives :: Map String (m [String]) }

makeLenses ''FactorState

makePrisms ''FItem

makeLenses ''FactorPrimitives

showType :: FItem -> String
showType (FInt _  ) = "Integer"
showType (FBol _  ) = "Bool"
showType (FIdt _  ) = "Identifier"
showType (FQut _  ) = "Quote"
showType (FWrd _ _) = "Word"

instance Show FItem where
 show (FInt i  ) = show i
 show (FBol b  ) = show b
 show (FIdt s  ) = s
 show (FQut q  ) = unwords (["["] ++ map show q ++ ["]"])
 show (FWrd n q) = unwords ([":", n] ++ map show q ++ [";"])

instance Show FactorError where
  show PopEmptyStack = "Tried to pop an empty stack"
  show (TypeError e r) = "Type error. Expected: " ++ e ++ "Received: " ++ r
  show (Unrecognised n) = "Unrecognised name: " ++ n
  show ParseError = "Parse error"

pop :: (MonadError FactorError m, MonadState FactorState m) => m FItem
pop = preuse (stack._Cons) >>= maybe (throwError PopEmptyStack) pop' where
  pop' (x,xs) = do
    stack .= xs
    return x

push :: MonadState FactorState m => FItem -> m ()
push x = stack %= cons x

scoped :: MonadState FactorState m => m a -> m a
scoped f = do
  m <- use vars
  x <- f
  vars .= m
  pure x

getNamed :: ( MonadState FactorState m
            , MonadError FactorError m
            , MonadReader (FactorPrimitives m) m )
         => String -> m [String]
getNamed n =
  use (vars . at n) >>=
  maybe (view (primitives . at n) >>=
           maybe (throwError . Unrecognised $ n)
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

-- | A class for Haskell types which have an equivalent Factor type
class FactorType a where embed :: Prism' FItem a
instance FactorType Integer where embed = _FInt
instance FactorType Bool where embed = _FBol

popType :: ( MonadState FactorState m
           , MonadError FactorError m
           , FactorType a )
        => m a
popType = do
  x <- pop
  case matching embed' x of
    Right y -> pure y
    Left t -> throwError $ TypeError "" (showType t)
    where embed' = embed

runOp :: ( MonadState FactorState m
         , MonadError FactorError m
         , FactorType a
         , FactorType b
         , FactorType c )
      => (a -> b -> c) -> m ()
runOp f = f <$> popType <*> popType >>= push . review embed

fact :: CharParsing m => IdentifierStyle m
fact =
  IdentifierStyle
    "factor"
    (noneOf "0123456789[]: \t\r\n")
    (noneOf " \t\r\n")
    ["[", "]", ":", "True", "False"]
    Identifier
    ReservedIdentifier

fItem :: (Monad m, TokenParsing m) => m FItem
fItem = choice
  [ FQut <$> brackets (some fItem) <?> "Quotation"
  , FWrd <$> (colon *> ident fact) <*> (some fItem <* semi) <?> "Word"
  , FBol <$> (reserve fact "True" $> True <|> reserve fact "False" $> False) <?> "Boolean"
  , FInt <$> natural <?> "integer"
  , FIdt <$> ident fact <?> "identifier" ]

tok :: ( MonadState FactorState m
       , MonadError FactorError m
       , MonadReader (FactorPrimitives m) m)
    => FItem -> m [String]

tok (FIdt n) = getNamed n
tok (FWrd n q) = [] <$ (vars . at n ?= q)
tok x = [] <$ push x

eval :: ( MonadState FactorState m
        , MonadError FactorError m
        , MonadReader (FactorPrimitives m) m )
     => [FItem] -> m [String]
eval = fmap concat . traverse tok

initPrimitives :: ( MonadError FactorError m
                  , MonadState FactorState m
                  , MonadReader (FactorPrimitives m) m )
               => FactorPrimitives m
initPrimitives = FactorPrimitives (fromList m) where
  m = (".", dot') : map (_2.mapped .~ [])
    [ ("+", intOp (+)), ("-", intOp (-)), ("*", intOp (*))
    , ("/", intOp div) , ("%", intOp mod)
    , ("lift", popType >>= lift'), ("sink", popType >>= sink), ("drop", void pop)
    , ("dup", pop >>= (\x -> push x *> push x))
    , ("if", bool <$> popType <*> pop <*> pop >>= push)
    , ("==", cmpOp (==)), ("!=", cmpOp (/=)), ("<=", cmpOp (<=))
    , (">=", cmpOp (>=)), ("<", cmpOp (<)), (">", cmpOp (>))
    , ("!", not <$> popType >>= push . review embed)
    , ("clear", stack .= [])
    , ("freeze", stack %= (pure . FQut))
    , ("empty", FBol <$> uses stack null >>= push)]
  cmpOp =
    runOp :: (MonadState FactorState m, MonadError FactorError m)
          => (Integer -> Integer -> Bool)
          -> m ()
  intOp =
    runOp :: (MonadState FactorState m, MonadError FactorError m)
          => (Integer -> Integer -> Integer)
          -> m ()
  bool True  t _ = t
  bool False _ f = f
  dot' = do
    x <- pop
    case x of
      FQut q -> eval q
      r -> pure [show r]
    -- (".",
    --   either (pure.show) eval . matching _FQut =<< pop)

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
  parsed <- parseWithError (many fItem) source
  result <- eval parsed
  stackt <- use stack
  unless (null stackt) . liftIO $ do
    putStr "Stack : "
    print stackt
  unless (null result) . liftIO $ do
    putStr "Result: "
    (putStrLn.unwords) result

-- | The Factor monad. This represents the result of evaluating a
-- Factor program.
newtype Factor a = Factor
  { _runFactor :: ReaderT (FactorPrimitives Factor) (StateT FactorState (EitherT FactorError IO)) a
  } deriving
    ( Functor, Applicative, Monad, MonadIO
    , MonadError FactorError, MonadState FactorState
    , MonadReader (FactorPrimitives Factor) )

main :: IO ()
main = eitherT print pure . flip evalStateT (FactorState mempty []) . flip runReaderT initPrimitives . _runFactor $ repl
