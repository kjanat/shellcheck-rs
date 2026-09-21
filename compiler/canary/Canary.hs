{-# LANGUAGE MagicHash #-}
module Canary (forward, constant, add, subtractInt, multiply, composed, chained, shared,
  eqInt, neInt, ltInt, leInt, gtInt, geInt, minimumInt, selectInt, nestedBranch) where

import GHC.Exts (Int#, (+#), (-#), (*#), (==#), (/=#), (<#), (<=#), (>#), (>=#))
import Helpers (first)

{-# NOINLINE forward #-}
forward :: Int# -> Int# -> Int#
forward x y = first y x

{-# NOINLINE constant #-}
constant :: Int# -> Int#
constant x = first 42# x

{-# NOINLINE add #-}
add :: Int# -> Int# -> Int#
add x y = x +# y

{-# NOINLINE subtractInt #-}
subtractInt :: Int# -> Int# -> Int#
subtractInt x y = x -# y

{-# NOINLINE multiply #-}
multiply :: Int# -> Int# -> Int#
multiply x y = x *# y

{-# NOINLINE composed #-}
composed :: Int# -> Int# -> Int#
composed x y = (x +# y) *# (x -# y)

{-# NOINLINE chained #-}
chained :: Int# -> Int# -> Int#
chained x y = first (add x y) (subtractInt x y) *# y

{-# NOINLINE shared #-}
shared :: Int# -> Int# -> Int#
shared x y = case add x y of
  z -> first (z *# y) z -# z

{-# NOINLINE eqInt #-}
eqInt :: Int# -> Int# -> Int#
eqInt x y = x ==# y

{-# NOINLINE neInt #-}
neInt :: Int# -> Int# -> Int#
neInt x y = x /=# y

{-# NOINLINE ltInt #-}
ltInt :: Int# -> Int# -> Int#
ltInt x y = x <# y

{-# NOINLINE leInt #-}
leInt :: Int# -> Int# -> Int#
leInt x y = x <=# y

{-# NOINLINE gtInt #-}
gtInt :: Int# -> Int# -> Int#
gtInt x y = x ># y

{-# NOINLINE geInt #-}
geInt :: Int# -> Int# -> Int#
geInt x y = x >=# y

{-# NOINLINE minimumInt #-}
minimumInt :: Int# -> Int# -> Int#
minimumInt x y = case x <# y of
  0# -> y
  _ -> x

{-# NOINLINE selectInt #-}
selectInt :: Int# -> Int# -> Int#
selectInt x y = case x of
  -9223372036854775808# -> y -# 1#
  -1# -> y *# 2#
  0# -> add y 7#
  1# -> subtractInt y 3#
  9223372036854775807# -> y +# 1#
  other -> first other y

{-# NOINLINE nestedBranch #-}
nestedBranch :: Int# -> Int# -> Int#
nestedBranch x y = case add x y of
  z -> case z <# x of
    0# -> case y ==# 0# of
      0# -> multiply z y
      _ -> subtractInt z 1#
    _ -> case x of
      0# -> first y z
      _ -> add z x
