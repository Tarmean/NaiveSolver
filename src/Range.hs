{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Range where
import qualified Data.Set as S
import qualified Data.Map as M
import Control.Monad.State
import Types (PSemigroup(..), POrd (..), PLattice ((<||>)))
import Control.Monad.Except (MonadError (..), runExceptT)
import Control.Monad.Trans.Except (ExceptT)
import Control.Applicative
import Debug.Trace

type Var = Int

someTest :: (Either (S.Set Var) (), SomeTest)
someTest = flip runState (SomeTest emptyPropEnv (S.singleton (Plus 1 2 3))) $ runExceptT $ do
  toRule @(Range Int) (out @(Range Int) 1 (Range (Just 1) (Just 3)))
  toRule  @(Range Int)(out @(Range Int) 2 (Range (Just 1) (Just 5)))
  plusProp @(Range Int)

pPlusAB, pPlusAR, pPlusBR  :: forall b f. (Num b, MonadProp b f) => PlusE Var -> f ()
pPlusAB (Plus a b r) = out @b r =<< (+) <$> ev a <*> ev b
pPlusAR (Plus a b r) = out @b b =<< (-) <$> ev r <*> ev a
pPlusBR (Plus a b r) = out @b a =<< (-) <$> ev r <*> ev b

plusProp :: forall s m s0. (
        Num s,
        POrd s,
        PSemigroup s,
        MonadState s0 m,
        Has s0 (S.Set Plus),
        Has s0 (PropEnv s)
    ) => ExceptT (S.Set Var) m ()
plusProp = appPropagator @s theProp
  where theProp e = toRule @s (pPlusAB @s e :: PropM m ()) *> toRule @s (pPlusAR @s e) *> toRule @s (pPlusBR @s e)

class (MonadError (Maybe (S.Set Var)) m) => MonadProp s m where
   tryEv :: Var -> m (Maybe s)
   out :: Var -> s -> m ()
class Monad m => DirtyM s m where
   diffVars :: m (S.Set Var)
ev :: (MonadProp s m) => Var -> m s
ev v = tryEv v >>= \case
   Nothing -> throwError Nothing
   Just s -> return s
type Prop s e = (Var -> Maybe e) -> s -> Maybe e


data PlusE s = Plus s s s
  deriving (Eq, Ord, Show, Foldable)
type Plus = PlusE Var

class CProp s e where
    prop :: Prop s e

-- instance CProp Plus e where
--   prop ev (Plus a b r) = do
--       ev a <- ev b


class GetNew c t | c -> t where
    getNew :: c -> S.Set Var -> [t]
class MonadProp s m => Prop1 s t m where
    prop1 :: t -> m ()

step :: forall s t m c. (GetNew c t, Prop1 s t m) => c -> S.Set Var -> m ()
step c v = forM_ (getNew c v) $ \t -> prop1 @s t
    

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

addElem :: (POrd s, PSemigroup s) => Var -> s -> S.Set Var -> PropEnv s -> Either (S.Set Var) (PropEnv s, Change)
addElem var s rns PropEnv {..} = case M.lookup var known of
    Nothing -> Right (PropEnv (S.insert var dirty) (M.insert var s known) (M.insert var rns reason), Replace)
    Just s' -> case compareP s s' of
                    Just GT -> Right (PropEnv (S.insert var dirty) (M.insert var s known) (M.insert var rns reason), Replace)
                    Nothing -> case s <?> s' of
                        Just s'' -> Right (PropEnv (S.insert var dirty) (M.insert var s'' known) (M.insertWith (<>) var rns reason), Join)
                        Nothing -> Left (rns <> M.findWithDefault S.empty var reason)
                    _ -> Right (PropEnv{..}, Noop)

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
instance (PSemigroup e, POrd e, MonadState s m, Has s (PropEnv e)) => MonadProp e (PropM m) where
  tryEv v = do
    addReason v
    gets ((M.!? v) . known . getL)
  out v s = do
    env <- gets (getL @_ @(PropEnv e))
    rns <- reasons
    case addElem v s rns env of
      Left cause -> throwError $ Just cause
      Right (env', _) -> modify (putL @_ @(PropEnv e) env')
instance (Monad m, Has s (PropEnv e)) => DirtyM e (StateT s m) where
  diffVars = gets (dirty . getL @_ @(PropEnv e))

data RuleResult = Success | HardFail (S.Set Var) | NotReady
toRule :: (MonadProp e (PropM m), Monad m) => PropM m () -> ExceptT (S.Set Var) m ()
toRule m = do
    me <- lift . evalTrackReadsT . runExceptT . runPropM $  m
    case me of
        Left Nothing -> pure ()
        Left (Just v) -> throwError v
        Right () -> pure ()

runRules :: forall v e t s m. (MonadState s m, Has s (PropEnv v), Has s t, GetNew t e) => (e -> ExceptT (S.Set Var) m ()) -> ExceptT (S.Set Var) m ()
runRules f = do
  struct <- gets (getL @_ @t)
  env <- gets (getL @_ @(PropEnv v))
  modify (putL @_ @(PropEnv v) (env { dirty = mempty }))
  let dirt = dirty env
  forM_ (getNew struct dirt) $ \v -> f v



appPropagator :: forall e f m s0. (
        MonadState s0 m,
        Has s0 (PropEnv e),
        Has s0 (S.Set (f Var)),
        GetNew (S.Set (f Var)) (f Var)
    ) => (f Var -> ExceptT (S.Set Var) m ()) -> ExceptT (S.Set Var) m ()
appPropagator  = runRules @e @(f Var) @(S.Set (f Var))


instance (Ord (f Var), Foldable f) => GetNew (S.Set (f Var)) (f Var) where
  getNew c v = [e | e <- S.toList c, any (`S.member` v) e]



data Range a = Range (Maybe a) (Maybe a) 
  deriving (Eq, Ord, Show)
instance (Ord a, Num a) => POrd (Range a) where
    compareP (Range a b) (Range a' b') = compare a a' `with` compare b' b
      where
        with LT LT = Just LT
        with EQ LT = Just LT
        with LT EQ = Just LT
        with GT GT = Just GT
        with EQ GT = Just GT
        with GT EQ = Just GT
        with EQ EQ = Just EQ
        with _ _ = Nothing
instance (Ord a, Num a) => PSemigroup (Range a) where
    (<?>) (Range a b) (Range a' b')
      | isEmpty l r = Nothing
      | otherwise = Just (Range l r)
      where
        l = (maxM a a')
        r = (minM b b')
        isEmpty (Just a) (Just b) = a > b
        isEmpty _ _ = False
minM :: Ord a => Maybe a -> Maybe a -> Maybe a
minM (Just a)  (Just b) = Just $ min a b
minM (Just a) _ = Just a
minM _ (Just a) = Just a
minM _ _ = Nothing

maxM :: Ord a => Maybe a -> Maybe a -> Maybe a
maxM (Just a)  (Just b) = Just $ max a b
maxM (Just a) _ = Just a
maxM _ (Just a) = Just a
maxM _ _ = Nothing
instance (Ord a, Num a) => PLattice (Range a) where
    (<||>) (Range a b) (Range a' b') = Just $ Range (minM a a') (maxM b b')

data SomeTest = SomeTest { testEnv :: (PropEnv (Range Int)), testPlus :: (S.Set Plus) }
  deriving (Eq, Ord, Show)
instance Has SomeTest (PropEnv (Range Int)) where
    getL =  testEnv
    putL v s = s { testEnv = v }
instance Has SomeTest (S.Set Plus) where
    getL =  testPlus
    putL v s = s { testPlus = v }

instance Num (Range Int) where
    Range a b + Range a' b' = Range (liftA2 (+) a a') (liftA2 (+) b b')
    Range a b - Range a' b' = Range (liftA2 (-) a b') (liftA2 (+) b a')
    
