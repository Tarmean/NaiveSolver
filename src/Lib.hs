module Lib
    ( someFunc
    ) where

import qualified Text.Pretty.Simple as P
import SmartShrinkTest (prettyWithKey, myShrinkTree, propLam, getValueFromInterleaved)
import SmartShrink (traceForest)
someFunc :: IO ()
someFunc = mapM_ print $ fmap (fmap prettyWithKey) $ traceForest (not . propLam . getValueFromInterleaved) $  myShrinkTree
