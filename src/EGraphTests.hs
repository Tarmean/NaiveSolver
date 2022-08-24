{-# Language DerivingStrategies, DeriveAnyClass, OverloadedStrings #-}
{-# Language LambdaCase #-}
{-# OPTIONS_GHC -Wno-orphans #-}
-- | Some more test cases, testing finite domain propagation with sudokus and some simple examples
module EGraphTests where
import qualified Data.Map as M
import Overeasy.EGraph
import FiniteDomains
import Data.Hashable
import EPropTest
import GHC.Generics ((:+:)(..))
import Range
import Prettyprinter
import Control.Monad.State hiding (StateT, modify', execStateT, runStateT, evalStateT)
import Control.Monad.Trans.State.Strict (execStateT)
import Data.BitVector as BV
import qualified IntLike.Map as ILM
import qualified Data.Foldable as F
import GHC.Generics(Generic)
import Control.DeepSeq (NFData)
import Boilerplate
import Data.Maybe (fromJust, mapMaybe)
import Data.List(transpose)
import Types
import Overeasy.Assoc (assocPartialLookupByValue)

data FiniteDomainF s a = DifferentFrom [a] | FDLiteral s
  deriving stock (Ord, Eq, Show, Generic, Functor, Foldable, Traversable)
  deriving anyclass (Hashable, NFData)

instance  EAnalysis (Range Integer) (FiniteDomainF a) where
    eaMake _ = pempty
    eHook _ = pure ()
instance  (Pretty a, Hashable a, Ord a, Enum a, Bounded a) => EAnalysis (FiniteDomain a) (FiniteDomainF a) where
    eaMake (DifferentFrom ls) = F.foldl' domDifference universe ls-- dumbArcConsistent pempty ls
    eaMake (FDLiteral l) = domSingleton l
    eHook cls = do
        dat <- eaClassData cls
        when (isBot dat) eaHalt
        case domPoint dat of 
            Just o -> do
              t <- eaAddTerm (FDLiteral o)
              eaMerge cls t
            Nothing -> pure ()

type Eg = EGraph (Range Integer) (ArithF :+: BoolF)
sudokuExample :: M.Map Int Int
sudokuExample = toIndex [
    "1  |  7| 9 ",
    " 3 | 2 |  8",
    "  9|6  |5  ",
    -------------
    "  5|3  |9  ",
    " 1 | 8 |  2",
    "6  |  4|   ",
    -------------
    "3  |   | 1 ",
    " 4 |   |  7",
    "  7|   |3  "
 ]
 where
   toIndex = M.fromList . mapMaybe2 toDig . zip [0..] . filter (/= '|') . concat
   toDig ' ' = Nothing
   toDig c = Just (fromEnum c - fromEnum '0')
   mapMaybe2 f = mapMaybe (traverse f)

printSudoku :: Eg2 -> IO ()
printSudoku = print . printGrid . toGrid
toGrid :: Eg2 -> M.Map Var (FiniteDomain SudokuNum)
toGrid eg0 = M.fromList [ (i-1, egLookupData eg0 (egLookupClass eg0 (inject $ Var i :: TermF EClassId))) | i <- [1..81] ]
  where
    egLookupNode :: Eg2 -> TermF EClassId -> ENodeId
    egLookupNode eg t = assocPartialLookupByValue t (egNodeAssoc eg)
    egLookupNodeClass :: Eg2 -> ENodeId -> EClassId
    egLookupNodeClass eg t = ILM.partialLookup t (egHashCons eg)
    egLookupClass :: Eg2 -> TermF EClassId -> EClassId
    egLookupClass eg = egLookupNodeClass eg . egLookupNode eg
    egLookupData eg c = snd $ eciData (ILM.partialLookup c (egClassMap eg))

testEg5 :: Maybe Eg2
testEg5 = flip execStateT egNew $ do
    v2 <- mkVar 2
    v3 <- mkVar 3
    _ <- egAddAnalysis v2 [(pempty, FD $ BV.fromList [2])]
    _ <- egAddAnalysis v3 [(pempty, FD $ BV.fromList [3])]
    _ <- egMerge v2 v3
    _ <- egRebuild'
    egCompact
    pure ()
testEg6 :: Eg2
testEg6 = fromJust $ flip execStateT egNew $ do
    v1 <- mkVar 62
    egAddAnalysis v1 [(pempty, FD $ BV.fromList [2])]

instance  (Pretty a, Num a, Integral a, Bounded a, Enum a, Ord a) => EAnalysis (FiniteDomain a) ArithF where
    eaMake = \case
        ArithPlusF a b -> a + b
        ArithMinusF a b -> a - b
        ArithTimesF a b -> a * b
        ArithModF a b -> mod a b
        ArithDivF a b -> div a b
        ArithTryDivF a b -> let out = div a b in if isBot out then top else out
        ArithConstF c -> fromIntegral c
        ArithShiftLF a l -> a * 2^l
        ArithShiftRF a l -> a `div` 2^l
        ArithInvDivF _ _ _ -> top
    eHook _ = pure ()


type Eg2 = EGraph (Range Integer, FiniteDomain SudokuNum) (ArithF :+: (FiniteDomainF SudokuNum) :+: VarF)
allDifferent :: (EAnalysisHook m (Range Integer, FiniteDomain SudokuNum)
                          (ArithF :+: (FiniteDomainF SudokuNum :+: VarF)), MonadState Eg2 m) => [EClassId] -> m ()
allDifferent ls = do
   forM_ (slices [] ls) $ \(x,xs) -> do
       (_, cls) <- egAddFlatTerm (R1 $ L1 (DifferentFrom xs))
       egMerge x cls
  where
    slices acc (x:xs) = (x,acc<>xs) : slices (x:acc) xs
    slices _ [] = []
    
type TermF = (ArithF :+: (FiniteDomainF SudokuNum) :+: VarF)
mkVar :: (EAnalysisHook m (Range Integer, FiniteDomain SudokuNum)
                          (ArithF :+: (FiniteDomainF SudokuNum :+: VarF)), MonadState Eg2 m) => Int -> m EClassId
mkVar v = fmap snd $ egAddFlatTerm (inject (Var v) :: TermF EClassId)
testEg4 :: Eg2
testEg4 = fromJust $ flip execStateT egNew $ do
    vs <- mapM mkVar [1..81]
    let vMap = M.fromList (zip [0..] vs)
        get1 x = case M.lookup x vMap of
            Just v -> v
            Nothing -> error ("testEg4: no such variable " <> show x)

    mapM_ (allDifferent . fmap get1) (rows <> cols <> squares)
    forM_ (M.toList sudokuExample) $ \(idx,dig) -> do
        let v = get1 idx
        egAddAnalysis v [(pempty, domSingleton (SD $ dig-1))]
    -- allDifferent [v1, v2, v3]
    egRebuild'
  where
    base = cellWidth * cellWidth
    rows = chunksOf base [0..base*base-1]
    cols = transpose rows
    squares = fmap concat $ concatMap (chunksOf cellWidth) $ transpose $ map (chunksOf cellWidth) rows


testEg :: Maybe Eg
testEg = flip execStateT egNew $ do
    (_,c1) <- egAddFlatTerm (inject $ (ArithConstF 1) )
    (_,c2) <- egAddFlatTerm (inject $  (ArithConstF 2))
    (_,_c1pc2) <- egAddFlatTerm (inject $ ArithPlusF c1 c2 )
    egRebuild'


testEg2, testEg3 :: Eg
testEg2 = fromJust $ flip execStateT egNew $ do
    (_,_c13) <- egAddFlatTerm (inject $ ArithConstF 3)
    (_,c1) <- egAddFlatTerm (inject $ (ArithConstF 1) )
    (_,c2) <- egAddFlatTerm (inject $  (ArithConstF 2))
    (_,_c1pc2) <- egAddFlatTerm (inject $ ArithPlusF c1 c2 )

    -- egMerge c13 c3
    egRebuild'

testEg3 = fromJust $ flip execStateT testEg2 $ do
    (_,c13) <- egAddFlatTerm (inject $ ArithConstF 1)
    _ <- egAddAnalysis c13 [1...1]
    egRebuild'
    pure ()
instance Pretty SudokuNum where
   pretty (SD s) = pretty (1+s)
instance (Enum s, Bounded s, Pretty s) => Pretty (FiniteDomain s) where
    pretty (FD a) = "Dom" <> (pretty (BV.toList a))
instance (Pretty (s), Pretty a) => Pretty (FiniteDomainF s a) where
    pretty (DifferentFrom xs) = "not-in" <+> (pretty xs)
    pretty (FDLiteral s) = pretty s
testEg7 :: Eg3
testEg7 = fromJust $ flip execStateT egNew $ do
    (_,c3) <- egAddFlatTerm (inject $ ArithConstF 3)
    (_,c7) <- egAddFlatTerm (inject $ (ArithConstF 7) )
    (_,_c1pc2) <- egAddFlatTerm (inject $ ArithModF c7 c3)
    egRebuild'
