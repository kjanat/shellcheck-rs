{-# LANGUAGE MagicHash #-}
module Canary (forward, constant, add, subtractInt, multiply, composed, chained, shared) where

import GHC.Exts (Int#, (+#), (-#), (*#))
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
