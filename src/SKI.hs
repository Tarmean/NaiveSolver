module SKI where


data DeBruijn = Abs DeBruijn | App DeBruijn DeBruijn | Var Int
  deriving (Eq, Ord, Show)


data SKI = S | K | I | SKI :@ SKI | T String
  deriving (Eq, Ord, Show)
infixl  8 :@

stepSKI :: SKI -> SKI
stepSKI (S :@ f :@ g :@ a) = f :@ a :@ (g :@ a)
stepSKI (K :@ a :@ _) = a
stepSKI (I :@ a) = a
stepSKI (f :@ a) = stepSKI f :@ a
stepSKI a = a

steps :: Int -> SKI -> IO ()
steps i = mapM_ print . take i . iterate stepSKI

test :: DeBruijn
test = Abs $ Abs (Abs $ Var 0)

toSKI :: DeBruijn -> SKI
toSKI = go 0
  where
    go inScope (Abs d) = go (inScope + 1) d
    go inScope (Var v) =  mkVar extraL extraR
      where
        extraL = v
        extraR = inScope - v - 1

    go inScope (App a b) = S :@ mkDups (inScope -1) (go inScope a) :@ (go inScope b)
      where
        mkDups 0 v = v
        mkDups i v 
          | i > 0 = S :@ (K :@ S) :@ mkDups (i - 1) v
        mkDups _ _ = error "toSKI: mkDups"



    dL e = K :@ e
    dR e = S :@ (K :@ e) :@ K
mkVar :: Int -> Int -> SKI
mkVar extraL extraR = goR extraR
  where
    goR i
      | i > 0 = dropR (goR (i - 1))
      | otherwise = goL extraL
    goL i 
      | i > 1 = dropL (goL (i - 1))
      | i == 1 = K
      | otherwise = I

dropR :: SKI -> SKI
dropR e = S :@ (K :@ e) :@ K

dropL :: SKI -> SKI
dropL e = K :@ I :@ e

