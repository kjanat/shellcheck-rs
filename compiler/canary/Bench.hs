{-# LANGUAGE MagicHash #-}
module Bench (benchSet, benchText, benchDeep, benchCps, benchChain, benchLoop) where

import GHC.Exts (Int(I#), Int#, (+#), (-#), (*#), (<=#))
import qualified Data.Set as Set

{-# NOINLINE benchSet #-}
benchSet :: Int# -> Int# -> Int
benchSet n seed = go n seed Set.empty
  where
    go i x s = case i <=# 0# of
      1# -> Set.size s
      _ -> let next = x *# 1103515245# +# 12345# in go (i -# 1#) next (Set.insert (I# next) s)

{-# NOINLINE benchText #-}
benchText :: Int# -> Int# -> Int#
benchText n k = spaces (map swap (sentence n k k)) 0#

{-# NOINLINE sentence #-}
sentence :: Int# -> Int# -> Int# -> [Char]
sentence n k c = case n <=# 0# of
  1# -> []
  _ -> case c of
    0# -> ' ' : sentence (n -# 1#) k k
    _ -> 'a' : sentence (n -# 1#) k (c -# 1#)

{-# NOINLINE swap #-}
swap :: Char -> Char
swap 'a' = 'b'
swap c = c

{-# NOINLINE spaces #-}
spaces :: [Char] -> Int# -> Int#
spaces [] n = n
spaces (' ' : cs) n = spaces cs (n +# 1#)
spaces (_ : cs) n = spaces cs n

{-# NOINLINE benchDeep #-}
benchDeep :: Int# -> Int# -> Int
benchDeep n k = deepSum (countdown n k)

{-# NOINLINE countdown #-}
countdown :: Int# -> Int# -> [Int]
countdown n k = case n <=# 0# of
  1# -> []
  _ -> I# k : countdown (n -# 1#) k

{-# NOINLINE deepSum #-}
deepSum :: [Int] -> Int
deepSum [] = 0
deepSum (I# x : xs) = case deepSum xs of
  I# rest -> I# (x +# rest)

{-# OPAQUE stepK #-}
stepK :: Int# -> (Int# -> Int#) -> Int#
stepK i k = k (i -# 1#)

{-# NOINLINE benchCps #-}
benchCps :: Int# -> Int# -> Int#
benchCps n k = loop n
  where
    loop i = case i <=# 0# of
      1# -> k
      _ -> stepK i loop

{-# NOINLINE benchChain #-}
benchChain :: Int# -> Int# -> Int
benchChain n k = lastOf (chain n (I# k))

{-# NOINLINE chain #-}
chain :: Int# -> Int -> [Int]
chain n prev = case n <=# 0# of
  1# -> []
  _ -> let next = prev + 1 in next : chain (n -# 1#) next

{-# NOINLINE lastOf #-}
lastOf :: [Int] -> Int
lastOf [] = 0
lastOf [x] = x
lastOf (_ : xs) = lastOf xs

{-# NOINLINE benchLoop #-}
benchLoop :: Int# -> Int -> Int
benchLoop n acc = case n <=# 0# of
  1# -> acc
  _ -> benchLoop (n -# 1#) (acc + 1)
