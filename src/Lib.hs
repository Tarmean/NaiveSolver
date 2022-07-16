module Lib
    ( someFunc
    ) where
import qualified EGraph.SimpleEgg as Data.SimpleEgg

someFunc :: IO ()
someFunc = Data.SimpleEgg.batchTest
