{-# LANGUAGE MagicHash #-}
module Helpers (first, crossPoly, crossApply, Sized(..), Described(..), Small(..)) where

import GHC.Exts (Int(I#), Int#, (+#), (*#))

{-# NOINLINE first #-}
first :: Int# -> Int# -> Int#
first x _ = x

{-# NOINLINE crossPoly #-}
crossPoly :: a -> b -> b
crossPoly _ y = y

{-# NOINLINE crossApply #-}
crossApply :: (a -> a) -> a -> a
crossApply f x = f x

{-# NOINLINE plusHelper #-}
plusHelper :: Int -> Int -> Int
plusHelper (I# a) (I# b) = I# (a +# b)

class Sized a where
  size :: a -> Int
  label :: a -> Int
  label _ = I# 11#

-- The superclass makes a `Described` dictionary carry a `Sized` one, so a
-- default method here reaches its methods through a superclass field.
class Sized a => Described a where
  describeIt :: a -> Int
  describeIt v = plusHelper (size v) (label v)
  weigh :: a -> Int
  weigh v = size v

data Small = Small Int

instance Sized Small where
  size (Small (I# n)) = I# (n *# 2#)

instance Described Small
