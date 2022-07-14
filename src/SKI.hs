module SKI where
import qualified Data.Set as S
-- Play with ideas from "λ to SKI, Semantically: Declarative Pearl"
-- which offers a linear translation from debruijn to SKI.
--
-- That counts the 'suc' terms, so it may still succs quadratically
-- But if we add buildin 'combinator * n' function it might work?
--
-- More concretely I want to play with SKI as stack machine
--
-- B op xs: offset op one slot further to the right
-- This gives B f g: run f and then g

data DeBruijnF f = Abs f (DeBruijnF f) | App f (DeBruijnF f) (DeBruijnF f) | Var f Int
  deriving (Eq, Ord, Show)
fOf :: DeBruijnF f -> f
fOf (Abs f _) = f
fOf (App f _ _) = f
fOf (Var f _) = f

-- go back and forth between initial and final encodings
-- we could stay in final or one-level views, but with laziness this isn't much worse and its simpler to start with

type DeBruijn = DeBruijnF ()
class Deb f where
    cAbs :: f -> f
    cApp :: f -> f -> f
    cVar :: Int -> f
instance Deb (S.Set Int) where
    cAbs f = S.map (\x -> x - 1) $ S.delete 0 f
    cApp f g = S.union f g
    cVar i = S.singleton i
instance Deb f => Deb (DeBruijnF f) where 
    cAbs r = Abs (cAbs $ fOf r) r
    cApp l r = App (cApp (fOf l) (fOf r)) l r
    cVar r = Var (cVar r) r

data SKI = S | K | I | Nest [SKI] [SKI] | T String | B | C | Times Int SKI
  deriving (Eq, Ord, Show)

nest :: SKI -> SKI -> SKI
nest (Nest l r) v = Nest l (v:r)
nest v (Nest l r) = Nest (v:l) r
nest a b = Nest [a,b] []


eval :: [SKI] -> [SKI]
eval ((Nest xs ys):zs) = xs <> reverse ys <> zs
eval (S:a:b:c:xs) = a : c : (nest b c) : xs
eval (K:a:_:xs) = a : xs
eval (B:a:b:c:xs) = a : nest b c : xs
eval (C:a:b:c:xs) = a:c:b:xs
eval (I:xs) = xs
eval (T s:xs) = T s:xs
eval (Times _ I:xs) = xs -- this kind of breaks laziness
eval (Times n B:x:xs) = appB n xs
  where
    appB 0 acc = x:acc
    appB i (Nest l r:v:ys) = appB (i-1) (Nest l (v:r):ys)
    appB i ls = Times i B :x:ls
eval (Times n K:x:xs) = appK n xs
  where
    appK 0 acc = x:acc
    appK i (_:ys) = appK (i-1) ys
    appK i ls = Times i K:x:ls
eval a = a

tc :: Deb a => DeBruijn -> DeBruijnF a
tc (Var _ i) = cVar i
tc (Abs _ r) = cAbs $ tc r
tc (App _ l r) = cApp (tc l) (tc r)


test :: DeBruijnF (S.Set Int)
test =  cAbs (cAbs (cApp (cVar 0) (cVar 1)))


data EnvUse = Drop Int | Take Int
  deriving (Eq, Ord, Show)
zipEnvs :: S.Set Int -> S.Set Int -> [EnvUse]
zipEnvs s1 s2 = go l0 r0
  where
    l0 = S.toDescList s1
    r0 = S.toDescList s2

    go (g:gs) (l:ls) = case compare g l of
        EQ -> addTake (go gs ls)
        GT -> addDrop (go gs (l:ls))
        LT -> error "illegal zip envs"
    go [] [] = []
    go xs [] = [Drop (length xs)]
    go _ _ = error "illegal zip envs"

    addTake (Take i : xs) = Take (i+1) : xs
    addTake xs = Take 1 : xs
    addDrop (Drop i : xs) = Drop (i+1) : xs
    addDrop xs = Drop 1 : xs
reverse3 :: [SKI]
reverse3 = [C,(Nest [B, C, nest C I] []), T "a", T "b", T "c"]
