module Lib
    ( someFunc
    ) where

import qualified Text.Pretty.Simple as P
import SmartShrinkTest (prettyWithKey, myShrinkTree, propLam, getValueFromInterleaved, shrinkTest2)
import SmartShrink (traceForest)
someFunc :: IO ()
someFunc = shrinkTest2 -- mapM_ print $ fmap (fmap prettyWithKey) $ traceForest (not . propLam . getValueFromInterleaved) $  myShrinkTree
