{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE NegativeLiterals #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
module Range where
import qualified Data.Set as S
import qualified Data.Map as M
import Control.Monad.State
import Types (PSemigroup(..), POrd (..), PLattice ((<||>)), PMonoid (pempty))
import Control.Monad.Except (MonadError (..), runExceptT)
import Control.Monad.Trans.Except (ExceptT)
import Control.Applicative
import Test.QuickCheck (quickCheck)
import Data.Maybe (isNothing)
import Debug.Trace (trace)

type Var = Int

-- Universal recipe to abstract a function: try all combinations of all possible inputs and pick the min/max results for the range
--
--   range1 / range2
--   ~
--   let results = [x / y | x <- [range1.min..range1.max], y <- [range2.min..range2.max]]
--   in minimum results ... maximum results
--
-- bruteForce turns any abstraction function into this brute force version
-- useful for checking that we have the best abstraction for the galois connection, i.e. extensionally bruteForce f == f
checkAbstraction :: (Range Int -> Range Int -> Range Int) -> IO ()
checkAbstraction f = quickCheck $ \x y -> f (fromTuple x) (fromTuple y) == bruteForce f (fromTuple x) (fromTuple y)

checkAbstraction1 :: (Range Int -> Range Int) -> IO ()
checkAbstraction1 f = quickCheck $ \x -> f (fromTuple x) == bruteForce f (fromTuple x)


testProp :: (Either (S.Set Var) (), SomeTest)
testProp = flip runState (SomeTest emptyPropEnv (S.singleton (Plus 1 2 3))) $ runExceptT $ do
  toRule (out @(Range Int) 1 (1...3))
  toRule (out @(Range Int) 2 (1...5))
  plusProp @(Range Int)


plusProp :: forall s m s0. (
        Num s,
        POrd s,
        PSemigroup s,
        MonadState s0 m,
        Has s0 (S.Set Plus),
        Has s0 (PropEnv s)
    ) => ExceptT (S.Set Var) m ()
plusProp = appPropagator @s theProp
  where
    theProp e = toRule (pPlusAB e) *> toRule (pPlusAR e) *> toRule (pPlusBR e)
    pPlusAB (Plus a b r) = out @s r =<< (+) <$> ev a <*> ev b
    pPlusAR (Plus a b r) = out @s b =<< (-) <$> ev r <*> ev a
    pPlusBR (Plus a b r) = out @s a =<< (-) <$> ev r <*> ev b

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
toRule :: (Monad m) => PropM m () -> ExceptT (S.Set Var) m ()
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
        isEmpty (Just x) (Just y) = x > y
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
    (<||>) a b
      | ia && ib = Nothing
      | ia = Just b
      | ib = Just a
      where
        ia = invalidRange a
        ib = invalidRange b
    (<||>) (Range a b) (Range a' b') = Just $ Range (minM a a') (maxM b b')

invalidRange :: Ord a => Range a -> Bool
invalidRange (Range (Just a) (Just b)) = a > b
invalidRange _ = False

data SomeTest = SomeTest { testEnv :: (PropEnv (Range Int)), testPlus :: (S.Set Plus) }
  deriving (Eq, Ord, Show)
instance Has SomeTest (PropEnv (Range Int)) where
    getL =  testEnv
    putL v s = s { testEnv = v }
instance Has SomeTest (S.Set Plus) where
    getL =  testPlus
    putL v s = s { testPlus = v }

minOf :: (Ord s, a ~ Maybe s) => (a -> a -> a) -> a -> a -> a -> a -> a
minOf f a b c d = minM (f b d) $ minM (f a c) $ minM (f a d) (f b c)
maxOf :: (Ord s, a ~ Maybe s) => (a -> a -> a) -> a -> a -> a -> a -> a
maxOf f a b c d = maxM (f b d) $ maxM (f a d) $ maxM (f a c) (f b c)
instance (Ord a, Num a) => Num (Range a) where
    Range a b + Range a' b' = Range (liftA2 (+) a a') (liftA2 (+) b b')
    Range a b - Range a' b' = Range (liftA2 (-) a b') (liftA2 (-) b a')
    Range a b * Range a' b' = Range (minOf (liftA2 (*)) a b a' b') (maxOf (liftA2 (*)) a b a' b')
    abs (Range Nothing b) = Range (abs <$> b) Nothing
    abs (Range (Just a) (Just b))
      | a <= 0 && b >= 0 = Range (Just 0) (Just $ max (abs a) (abs b))
      | otherwise = sortRange (Just $ abs a) (Just $ abs b)
    abs (Range a Nothing) = Range (min 0 <$> a) Nothing
    signum (Range l r) = case lb <?> rb of
        Just a -> a
        Nothing -> Range (Just 1) (Just 0)
      where
        lb = case l of
          Nothing -> Range Nothing Nothing
          Just a 
            | a > 0 -> Range (Just 1) Nothing
            | a == 0 -> Range (Just 0) Nothing
            | otherwise -> Range (Just (-1)) Nothing
        rb = case r of
          Nothing -> Range Nothing Nothing
          Just b 
            | b < 0 -> Range Nothing (Just (-1))
            | b == 0 -> Range Nothing (Just 0)
            | otherwise -> Range Nothing (Just 1)
    fromInteger i = Range (Just $ fromInteger i) (Just $ fromInteger i)
    negate r
      | invalidRange r = r
    negate (Range a b) = Range (negate <$> b) (negate <$> a)
instance (Ord a, Real a) => Real (Range a) where
  toRational = undefined
instance (Integral a, Eq a) => Enum (Range a) where
  toEnum i = Range (Just $ fromIntegral i) (Just $ fromIntegral i)
  fromEnum (Range (Just i) (Just j)) | i == j = fromIntegral i
  fromEnum _ = undefined
instance (Ord a, Bounded a, Integral a) => Integral (Range a) where
  div (Range ma mb) (Range mc md) = Range (minOf f ma mb mc md) (maxOf g ma mb mc md)
    where
      f x y = case (x, y) of
          (Just a, Just d)
            | d /= 0 -> Just $ a `div` d
            | otherwise -> Just maxBound
          _ -> Nothing
      g x y = case (x, y) of
          (Just a, Just d)
            | d /= 0 -> Just $ a `div` d
            | otherwise -> Just minBound
          _ -> Nothing
  divMod = undefined
  toInteger = undefined
  quotRem = undefined

(...) :: (Ord a, Num a) => a -> a -> Range a
(...) a b = Range (Just a) (Just b)
-- >>> 1 * 2...3 + 4...5
testRange :: Range Int
testRange = 2 * 2...3 + 4...5
-- x \subset sqrtI x ^2
monotonicFloat :: (Double -> Double) -> Range Int -> Range Int
monotonicFloat f (Range a b) = Range (ceiling . f . fromIntegral <$> a) (floor . f . fromIntegral <$> b)
-- monotonicFloat2 :: (Double -> Double) -> Range Int -> Range Int
-- monotonicFloat f (Range a b) = Range (ceiling . f . fromIntegral <$> a) (floor . f . fromIntegral <$> b)
sqrtI :: Range Int -> Range Int
sqrtI = monotonicFloat sqrt

data MaybeInf a = NegInf | Finite a | PlusInf 
  deriving (Eq, Ord, Show)
smallestPos :: (Ord a, Num a) => Range a -> Maybe a
smallestPos (Range (Just a) (Just b))
  | a <= 0 && b > 0 = Just 1
  | a >= 0 = Just a
  | otherwise = Nothing
smallestPos (Range Nothing (Just a))
  | a > 0 = Just 1
  | otherwise = Nothing
smallestPos (Range (Just a) Nothing)
  | a <= 0 = Just 1
  | otherwise = Just a
smallestPos _ = Just 1
smallestNeg :: (Ord a, Num a) => Range a -> Maybe a
smallestNeg = fmap negate . smallestPos . flipRange
flipRange :: Num a => Range a -> Range a
flipRange (Range a b) = Range (negate <$> b) (negate  <$> a)
largestPos :: (Ord a, Num a) => Range a -> Maybe (MaybeInf a)
largestPos (Range _ (Just b))
  | b >= 0 = Just $ Finite b
  | otherwise = Nothing
largestPos _ = Just PlusInf
largestNeg :: (Ord a, Num a) => Range a -> Maybe (MaybeInf a)
largestNeg (Range (Just a) _)
  | a <= 0 = Just $ Finite a
  | otherwise = Nothing
largestNeg _ = Just NegInf

appDiv :: (Integral a, Ord a, Num a) => MaybeInf a -> MaybeInf a -> Maybe (MaybeInf a)
appDiv PlusInf PlusInf= Just $ Finite 1
appDiv NegInf NegInf= Just $ Finite 1
appDiv PlusInf NegInf= Just $ Finite (-1)
appDiv NegInf PlusInf= Just $ Finite (-1)
appDiv _ PlusInf = Just $ Finite 0
appDiv _ NegInf = Just $ Finite 0
appDiv PlusInf Finite{} = Just PlusInf
appDiv NegInf Finite{} = Just NegInf
appDiv (Finite _) (Finite 0) = Nothing
appDiv (Finite a) (Finite b) = Just $ Finite $ a `div` b

appMod :: (Integral a, Ord a, Num a) => MaybeInf a -> MaybeInf a -> Maybe (MaybeInf a)
appMod PlusInf PlusInf = Just $ Finite 0
appMod NegInf NegInf = Just $ Finite 0
appMod PlusInf NegInf = Just $ Finite 0
appMod NegInf PlusInf = Just $ Finite 0
appMod (Finite a) PlusInf = Just $ Finite a
appMod (Finite a) NegInf = Just $ Finite (negate a)
appMod PlusInf (Finite a) = Just (Finite a)
appMod NegInf (Finite a) = Just (Finite a)
appMod (Finite _) (Finite 0) = Nothing
appMod (Finite a) (Finite b) = Just $ Finite $ a `mod` b


-- modI :: Range Int -> Range Int -> Range Int
-- modI l r
--   | null combis = Range (Just 1) (Just 0)
--   | otherwise = toRange (minimum combis) (maximum combis)
--   where combis = [ o | a <- extremePoints l, Just b <- markantPoints r, Just o <- [appMod a b]]
divI :: Range Int -> Range Int -> Range Int
divI l r
  | null combis = Range (Just 1) (Just 0)
  | otherwise = toRange (minimum combis) (maximum combis)
  where combis = [ o | a <- extremePoints l, Just b <- markantPoints r, Just o <- [appDiv a b]]


-- Doing case splitting rather then brute-forcing all relevant points is much faster
-- The inner divG only considers the case where the divisor is strictly positive
divB :: (Show a, Integral a) => Range a -> Range a -> Range a
divB a b = case splitPosNeg b of
    Just (lb,rb) -> case (negate (divG a (negate lb))) <||> divG a rb of
        Just o -> o
        Nothing -> Range (Just 1) (Just 0)
    Nothing 
      | isPos b -> divG a b
      | otherwise -> negate (divG a (negate b))
  where
    divG :: (Show a, Integral a, Num a) => Range a -> Range a -> Range a
    divG x y
      | invalidRange x || invalidRange y = Range (Just 1) (Just 0)
    -- divisor is positive: divide by c to keep large, divide by d to move towards 0
    divG (Range x y) (Range c d)
      | x >= Just 0 = Range (x `divM` d) (y `divM` c) -- strictly positive, shrink min
      | isNothing y || y >= Just 0 = Range (x `divM` c) (y `divM` c) -- mixed signs, keep both
      | otherwise = Range (x `divM` c) (y `divM` d) -- strictly negative, shrink max
      where
        divM Nothing _ = Nothing
        divM _ Nothing = Just 0
        divM (Just l) (Just r) = Just $ l `div` r

isPos :: (Num a, Ord a) => Range a -> Bool
isPos (Range (Just a) _) = a > 0
isPos _ = False

splitPosNeg :: (Num a, Ord a) => Range a -> Maybe (Range a, Range a)
splitPosNeg (Range Nothing Nothing) = Just (Range Nothing (Just $ -1), Range (Just 1) Nothing)
splitPosNeg (Range Nothing (Just b))
  | b >= 0 = Just (Range Nothing (Just $ -1), Range (Just 1) (Just b))
splitPosNeg (Range (Just a) Nothing)
    | a <= 0 = Just (Range (Just a) (Just $ -1), Range (Just 1) Nothing)
splitPosNeg (Range (Just a) (Just b))
  | a <= 0 && b >= 0 = Just (Range (Just a) (Just $ -1), Range (Just 1) (Just b))
splitPosNeg _ = Nothing


extremePoints :: (Ord a, Num a) => Range a -> [MaybeInf a]
extremePoints (Range x y) = [x', y']
  where
    x' = case x of
      Just a -> Finite a
      Nothing -> NegInf
    y' = case y of
      Just a -> Finite a
      Nothing -> PlusInf
markantPoints :: (Ord a, Num a) => Range a -> [Maybe (MaybeInf a)]
markantPoints r = [Finite <$> (smallestPos r), largestPos r, Finite <$> (smallestNeg r), largestNeg r]
toRange :: MaybeInf a -> MaybeInf a -> Range a
toRange (NegInf) PlusInf = Range Nothing Nothing
toRange (Finite a) PlusInf = Range (Just a) Nothing
toRange (NegInf) (Finite a) = Range Nothing (Just a)
toRange (Finite a) (Finite b) = Range (Just a) (Just b)
toRange _ _ = error "impossible"

data Interval a = I a a
  deriving (Eq, Ord, Show)
idiv :: Integral a => Interval a -> Interval a -> Interval a
idiv (I l u) (I l' u') =
  if l' <= 0 && 0 <= u' then undefined else I
    (min (l `Prelude.div` max 1 l') (u `Prelude.div` min (-1) u'))
    (max (u `Prelude.div` max 1 l') (l `Prelude.div` min (-1) u'))

-- min (a...b mod x)
-- if b-a >= x then 0
--
--r = a+z
--, z < x
-- offset = a mod x
-- (a+z) mod x
--
-- offset + z >= x = offset+z - x
-- otherwise = offset+z
--
-- solve for minimum:
--
-- if (a `mod` x + (b-a)) > x
-- then 0
-- else a
--
-- max:
-- if (a `mod` x + (b-a)) >= x
-- then x-1
-- else b `mod` x


bruteForce :: forall r. (LiftRange r r) => r -> r
bruteForce f = liftRange [f]

class LiftRange a b where
    liftRange :: [a] -> b
instance (LiftRange a r, Enum x) => LiftRange (Range x -> a) (Range x -> r) where
    liftRange :: [Range x -> a] -> Range x -> r
    liftRange fs (Range (Just a) (Just b)) = liftRange [f (mkRange v) | f <- fs, v <- [a..b]]
    liftRange _ _ = error "liftRange: cannot brute force infinite range"
instance (Show a, Num a, Ord a) => LiftRange (Range a) (Range a) where
    liftRange :: [Range a] -> Range a
    liftRange [] = Range (Just 1) (Just 0)
    liftRange a = foldl1 step a
      where
        step l r = case l <||> r of
            Nothing -> Range (Just 1) (Just 0)
            Just l' -> l'
instance (Num a, Ord a) => PMonoid (Range a) where
   pempty = Range Nothing Nothing
mkRange :: x -> Range x
mkRange x = Range (Just x) (Just x)

fromTuple :: Ord a => (a, a) -> Range a
fromTuple (a, b) = sortRange (Just a) (Just b)



rangeMax :: Range r -> Maybe r
rangeMax (Range _ (Just b)) = Just b
rangeMax _ = Nothing
rangeMin :: Range r -> Maybe r
rangeMin (Range (Just a) _) = Just a
rangeMin _ = Nothing

minimumMaybe :: Ord a => [Maybe a] -> Maybe a
minimumMaybe = foldl1 step
  where
    step (Just a) (Just b) = Just (min a b)
    step _ _ = Nothing
maximumMaybe :: Ord a => [Maybe a] -> Maybe a
maximumMaybe = foldl1 step
  where
    step (Just a) (Just b) = Just (max a b)
    step _ _ = Nothing
    
-- instance TestRangeGalois (Range a -> r) where
-- testRangeGalois :: (Enum t, Ord a) => Range t -> (t -> a) -> Range a

sortRange :: Ord a => Maybe a -> Maybe a -> Range a
sortRange (Just a) (Just b)
  | a > b = Range (Just b) (Just a)
sortRange a b = Range a b

emptyRange :: Num a => Range a
emptyRange = Range (Just 1) (Just 0)
