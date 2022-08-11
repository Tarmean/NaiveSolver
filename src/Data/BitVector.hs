{-# LANGUAGE ScopedTypeVariables #-}
module Data.BitVector where


import Data.Word
import Data.List (foldl')

import Data.Bits
import Data.Hashable

newtype BitArray a = BitArray { unBitArray :: Word16 }
  deriving (Eq, Ord, Show, Hashable)

singleton :: Enum a => a -> BitArray a
singleton = BitArray . toBits

empty :: BitArray a
empty = BitArray 0
union :: BitArray a -> BitArray a -> BitArray a
union (BitArray a) (BitArray b) = BitArray (a .|. b)
intersection :: BitArray a -> BitArray a -> BitArray a
intersection (BitArray a) (BitArray b) = BitArray (a .&. b)
difference :: BitArray a -> BitArray a -> BitArray a
difference (BitArray a) (BitArray b) = BitArray (a .&. complement b)
delete :: Enum a => a -> BitArray a -> BitArray a
delete x b = difference b (singleton x)



isSubsetOf :: BitArray a -> BitArray a -> Bool
isSubsetOf (BitArray a) (BitArray b) = a .&. b == a
filterS :: (Bounded a, Enum a) => (a -> Bool) -> BitArray a -> BitArray a
filterS f = fromList . filter f . toList

mapS :: (Bounded a, Enum a) => (a -> a) -> BitArray a -> BitArray a
mapS f = fromList . map f . toList
null :: BitArray a -> Bool
null (BitArray a) = a == 0


toList :: forall a. (Bounded a, Enum a) => BitArray a -> [a]
toList ba =
 filter (`member` ba) [minBound .. (maxBound :: a)]
    

toBits :: (Enum a) => a -> Word16
toBits = bitTable . fromEnum
insert :: (Enum a) => a -> BitArray a -> BitArray a
insert a = BitArray . (.|.) (toBits a) . unBitArray

member :: Enum a => a -> BitArray a -> Bool
member a (BitArray w) = w .&.toBits a /= zeroBits

size :: BitArray a -> Int
size (BitArray a) = popCount a

bitTable :: Int -> Word16
bitTable 0 = 0b000000001
bitTable 1 = 0b000000010
bitTable 2 = 0b000000100
bitTable 3 = 0b000001000
bitTable 4 = 0b000010000
bitTable 5 = 0b000100000
bitTable 6 = 0b001000000
bitTable 7 = 0b010000000
bitTable 8 = 0b100000000
bitTable _ = error "Unreachable"
bitMask :: Word16
bitMask = 0b111111111
flipSet :: BitArray a -> BitArray a
flipSet (BitArray w) = BitArray $ complement w .&. bitMask


-- | Construct from a list of set bits.
{-# INLINABLE fromList #-}
fromList :: (Enum a) => [a] -> BitArray a
fromList = BitArray . foldl' (.|.) 0 . fmap toBits
