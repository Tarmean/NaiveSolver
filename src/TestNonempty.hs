-- {-# OPTIONS_GHC -ddump-simpl -dsuppress-all -dsuppress-uniques -O2 -fforce-recomp #-}
module TestNonempty (bar, baz) where

import qualified Data.List.NonEmpty as NE


foo :: [a] -> Maybe a
foo a = NE.head <$> (NE.nonEmpty a)


bar :: Int
bar = case foo [1..10] of
    Nothing -> error "Can't happen"
    Just x -> x


baz :: Int
baz = head [1..10]
