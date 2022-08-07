{-# LANGUAGE LambdaCase #-}
module EggProp where



import Overeasy.EGraph
import Overeasy.Assoc
import Control.Monad.State
import qualified Data.Map as M
import qualified Data.Set as S
import Control.Lens
import qualified Data.List as L
import qualified IntLike.Map as ILM


        -- _1 %= \eg -> execState (egAddTerm q term1)
        -- undefined
    -- goId cid2 = do
    --  use (_2 . at cid2) >>= \case
    --      Just cid1 -> pure cid1
    --      Nothing -> do
    --          let class2 = (ILM.partialLookup cid2 (egClassMap eg2))
    --          let termsInClass = map (`assocPartialLookupByKey` egNodeAssoc eg2) (eciNodes class2)
    --              smallestFirst 
    --  (nid2, assocPartialLookupByKey nid2 (egNodeAssoc eg2))
    -- go (nid2, term2) = do
    --     term1 <- traverse goId term2


    --     pure undefined
    --
