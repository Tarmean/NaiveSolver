{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeFamilies #-}
module Propagator where
import qualified Data.Set as S
import Types
import Control.Monad.Except
import Control.Monad.State
import qualified Data.Map as M
import Range
import Data.Typeable
import Debug.Trace (traceM)

testProp :: (Either (S.Set Var) (), SomeTest)
testProp = flip runState (SomeTest emptyPropEnv emptyPropEnv (S.singleton (Plus 1 2 3)) (S.singleton (LessEqThan 5 3 1))) $ runExceptT $ do
  toRule (out @(Val Bool) "" 5 (Val True))
  toRule (out @(Range Int) "" 1 (1...20))
  toRule (out @(Range Int) "" 2 (1...20))
  toRule (out @(Range Int) "" 3 (2...2))


  fixPropsN 2


-- x : 1...1
-- y: 1...1
-- z: x+y
-- z <= x
--
-- z: 2...1


fixPropsN :: (MonadState SomeTest m) => Int -> ExceptT (S.Set Int) m ()
fixPropsN 0 = pure ()
fixPropsN i = do
  theProps >>= \case
    False -> pure ()
    True -> fixPropsN (i-1)

data PlusE s = Plus s s s
  deriving (Eq, Ord, Show, Foldable)
type Plus = PlusE Var
type APropC s m s0 = (
        PSemigroup s,
        MonadState s0 m,
        Has s0 (PropEnv s)
    )

class (MonadState s0 m) => PropsFor m s0 where
    theProps :: ExceptT (S.Set Var) m Bool
instance (MonadState SomeTest m) => PropsFor m SomeTest  where
  theProps = do
     dirtBool <- popDirty @(Val Bool)
     onStruct @(S.Set LessEqThan) dirtBool (lessEqThanProp @Int)

     dirtInt <- popDirty @(Range Int)
     onStruct @(S.Set Plus) dirtInt (plusProp @(Range Int))
     onStruct @(S.Set LessEqThan) dirtInt (lessEqThanProp @Int)
     pure (not $ S.null dirtBool && S.null dirtInt)
type AProp p m s0 = ExceptT (S.Set Var) m ()

plusProp :: forall s m s0. (Debug s, Num s, PContains s, APropC s m s0) => Plus -> AProp Plus m s0
plusProp = theProp
  where
    theProp e = toRule (pPlusAB e) *> toRule (pPlusAR e) *> toRule (pPlusBR e)
    pPlusAB (Plus a b r) = out @s "plusAB"  r =<< (+) <$> ev a <*> ev b
    pPlusAR (Plus a b r) = out @s "plusAR" b =<< (-) <$> ev r <*> ev a
    pPlusBR (Plus a b r) = out @s "plusBR" a =<< (-) <$> ev r <*> ev b

data LessEqThanE s = LessEqThan { isTrue :: s, lhs :: s, rhs :: s }
    deriving (Eq, Ord, Show, Foldable)
type LessEqThan = LessEqThanE Var
lessEqThanProp :: forall s m s0. (Debug s, Num s, Ord s, APropC (Val Bool) m s0, APropC (Range s) m s0) => LessEqThan ->  AProp LessEqThan m s0
lessEqThanProp = (\x -> propLR x *> propRL x *> propTruthy x)
  where
  propLR (LessEqThan {..}) = toRule $ do
    Val truthy <- ev @(Val Bool) isTrue
    r <- ev @(Range s) rhs 
    case truthy of
      True -> do
        out "leqLR1" lhs (upperBound r)
      False -> out "leqLR2" lhs ((\x -> x - 1) <$> lowerBound r)
  propRL (LessEqThan {..}) = toRule $ do
    Val truthy <- ev @(Val Bool) isTrue
    l <- ev @(Range s) lhs 
    case truthy of
      True -> out ("leqRL1") rhs (lowerBound l)
      False -> out "leqRL2" rhs ((+1) <$> upperBound l)
  propTruthy (LessEqThan {..}) = toRule $ do
     l <- ev @(Range s) lhs
     r <- ev @(Range s) rhs
     case compareP l r of
         Nothing -> pure ()
         Just GT -> out ("leqFalse" <> show (l,r))  isTrue (Val False)
         _ -> out "leqTrue" isTrue (Val True)

   

whenVar :: (MonadProp s m) => Var -> (s -> Bool) -> m () -> m ()
whenVar v p m= do
   s <- ev v
   if p s
   then m
   else return ()
        
class (MonadError (Maybe (S.Set Var)) m) => MonadProp s m where
   tryEv :: Var -> m (Maybe s)
   out :: String -> Var -> s -> m ()
class Monad m => DirtyM s m where
   diffVars :: m (S.Set Var)
ev :: (MonadProp s m) => Var -> m s
ev v = tryEv v >>= \case
   Nothing -> throwError Nothing
   Just s -> return s
outOver :: forall s m. MonadProp s m => String -> s -> (s -> s) -> Var -> m ()
outOver dbgs zer f v = do
    mo <- tryEv v
    case mo of
      Nothing -> out dbgs v (f zer)
      Just o -> out dbgs v (f o)
type Prop s e = (Var -> Maybe e) -> s -> Maybe e




class GetNew c t | c -> t where
    getNew :: c -> S.Set Var -> [t]
class MonadProp s m => Prop1 s t m where
    prop1 :: t -> m ()

data PropEnv e = PropEnv {
    dirty :: S.Set Var,
    known :: M.Map Var e,
    reason :: M.Map Var (S.Set Var)
}
  deriving (Eq, Ord, Show)
emptyPropEnv :: PropEnv e
emptyPropEnv = PropEnv S.empty M.empty M.empty
class Has s t where
    getL :: s -> t
    putL :: t -> s -> s
setDirty :: Var -> PropEnv s -> PropEnv s
setDirty v (PropEnv d k r) = PropEnv (S.insert v d) k r 
withReasons :: Var -> S.Set Var -> PropEnv s -> PropEnv s
withReasons v r (PropEnv d k r') = PropEnv d k (M.insertWith const v r r')

class Monad m => MonadReason m where
    addReason :: Var -> m ()
    reasons :: m (S.Set Var)
instance MonadReason m => MonadReason (StateT s m) where
    addReason  = lift . addReason
    reasons = lift reasons

data Change = Noop | Replace | Join

newtype TrackReadsT m a = TrackReadsT { runTrackReadsT :: StateT (S.Set Var) m a }
    deriving (Functor, Applicative, Monad, MonadTrans)
evalTrackReadsT :: Monad m => TrackReadsT m a -> m a
evalTrackReadsT m = evalStateT (runTrackReadsT m) S.empty


instance Monad m => MonadReason (TrackReadsT m) where
    addReason v = TrackReadsT $ modify (S.insert v)
    reasons = TrackReadsT get

type Debug e = (Show e, Typeable e)
dbg :: Applicative f => String -> f ()
dbg s = pure () -- traceM s

addElem :: forall s. (Debug s, PSemigroup s, PContains s) => String -> Var -> s -> S.Set Var -> PropEnv s -> Either (S.Set Var) (PropEnv s, Change)
addElem dbgS var new rns PropEnv {..} = case M.lookup var known of
    Nothing -> Right (PropEnv (S.insert var dirty) (M.insert var new known) (M.insert var rns reason), Replace)
    Just old -> case compareC new old of
                    Just LT -> do
                      dbg ("Replace(" <> showType @s  <> "-" <> dbgS <> ") v" <> show var <> ": " <> show old <> " -> " <> show new)
                      Right (PropEnv (S.insert var dirty) (M.insert var new known) (M.insert var rns reason), Replace)
                    Nothing -> case new <?> old of
                        Just new' -> do
                          dbg ("Update(" <> showType @s  <> "-" <> dbgS <> ") v" <> show var <> ": " <> show old <> " && " <> show new <> " => " <> show new')
                          Right (PropEnv (S.insert var dirty) (M.insert var new' known) (M.insertWith (<>) var rns reason), Join)
                        Nothing -> do
                          dbg ("Update Failed(" <> showType @s  <> "-" <> dbgS <> ") v" <> show var <> ": " <>  show old <> " && " <> show new <> " => FALSE")
                          Left (rns <> M.findWithDefault S.empty var reason)
                    _ -> do
                      dbg ("Noop(" <> showType @s  <> "-" <> dbgS <> ") v" <> show var <> ": " <> show old <> " -/-> " <> show new)
                      Right (PropEnv{..}, Noop)

instance MonadReason m => MonadReason (ExceptT e m) where
  addReason = lift . addReason
  reasons = lift reasons
newtype PropM m a = PropM { runPropM :: ExceptT (Maybe (S.Set Var)) (TrackReadsT m) a }
    deriving (Functor, Applicative, Monad, MonadReason, MonadError (Maybe (S.Set Var)))
instance MonadState s m => MonadState s (PropM m) where
    get = PropM $ lift $ lift get
    put = PropM . lift . lift . put
instance MonadTrans PropM where
    lift = PropM . lift . lift
instance (Debug e, PSemigroup e, PContains e, MonadState s m, Has s (PropEnv e)) => MonadProp e (PropM m) where
  tryEv v = do
    addReason v
    gets ((M.!? v) . known . getL)
  out dbgS v s = do
    env <- gets (getL @_ @(PropEnv e))
    rns <- reasons
    case addElem dbgS v s rns env of
      Left cause -> throwError $ Just cause
      Right (env', _) -> modify (putL @_ @(PropEnv e) env')

showType :: forall s. Typeable s => String
showType = show $ typeRep (Proxy :: Proxy s)
instance (Monad m, Has s (PropEnv e)) => DirtyM e (StateT s m) where
  diffVars = gets (dirty . getL @_ @(PropEnv e))

data RuleResult = Success | HardFail (S.Set Var) | NotReady
toRule :: (Monad m) => PropM m () -> ExceptT (S.Set Var) m ()
toRule m = do
    me <- lift . evalTrackReadsT . runExceptT . runPropM $  m
    case me of
        Left Nothing -> pure ()
        Left (Just v) -> throwError v
        Right () -> pure ()

runRules :: forall v e t s m. (MonadState s m, Has s (PropEnv v), Has s t, GetNew t e) => (e -> ExceptT (S.Set Var) m ()) -> ExceptT (S.Set Var) m ()
runRules f = do
  dirt <- popDirty @v
  struct <- gets (getL @_ @t)
  forM_ (getNew struct dirt) $ \v -> f v

onStruct :: forall t e s0 m. ( MonadState s0 m, Has s0 t, GetNew t e) => S.Set Var -> (e -> ExceptT (S.Set Var) m ()) -> ExceptT (S.Set Var) m ()
onStruct  dirt f = do
  struct <- gets (getL @_ @t)
  forM_ (getNew struct dirt) $ \v -> f v


popDirty :: forall v m s0. ( Monad m, Has s0 (PropEnv v), Has s0 (PropEnv v), MonadState s0 m) => (m (S.Set Var))
popDirty  = do
  env <- gets (getL @_ @(PropEnv v))
  modify (putL @_ @(PropEnv v) (env { dirty = mempty }))
  pure (dirty env)





instance (Ord (f Var), Foldable f) => GetNew (S.Set (f Var)) (f Var) where
  getNew c v = [e | e <- S.toList c, any (`S.member` v) e]
data SomeTest = SomeTest { testBool :: (PropEnv (Val Bool)),testEnv :: (PropEnv (Range Int)), testPlus :: (S.Set Plus), testLEQ :: (S.Set LessEqThan) }
  deriving (Eq, Ord, Show)
instance Has SomeTest (PropEnv (Val Bool)) where
    getL =  testBool
    putL v s = s { testBool = v }
instance Has SomeTest (PropEnv (Range Int)) where
    getL =  testEnv
    putL v s = s { testEnv = v }
instance Has SomeTest (S.Set Plus) where
    getL =  testPlus
    putL v s = s { testPlus = v }
instance Has SomeTest (S.Set LessEqThan) where
    getL =  testLEQ
    putL v s = s { testLEQ = v }
