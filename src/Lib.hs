module Lib
    ( someFunc
    ) where

import qualified Text.Pretty.Simple as P
import EPropTest
import SmartShrinkTest (prettyWithKey, propLam, getValueFromInterleaved, shrinkTest2)
import Data.Maybe
import SmartShrink (traceForest)
someFunc :: IO ()
someFunc = printSudoku $ fixChoice testEg4
-- someFunc = shrinkTest2 -- mapM_ print $ fmap (fmap prettyWithKey) $ traceForest (not . propLam . getValueFromInterleaved) $  myShrinkTree
