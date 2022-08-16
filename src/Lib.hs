module Lib
    ( someFunc
    ) where

import EPropTest
import BFSChoiceTree
import Data.Utils

someFunc :: IO ()
someFunc = pprint $ fmap (fmap extractVars) (BFSChoiceTree.mkTree 10 gamePlan aocRiddle)

-- pprint $ valOf $ mkTree [(EClassId 0, 1, 9), (EClassId 1, 1, 9), (EClassId 2, 1, 9), (EClassId 3, 1, 9), (EClassId 4, 1, 9)]
-- someFunc = shrinkTest2 -- mapM_ print $ fmap (fmap prettyWithKey) $ traceForest (not . propLam . getValueFromInterleaved) $  myShrinkTree
