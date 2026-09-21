{-# LANGUAGE MagicHash #-}
module Canary (forward, constant) where

import GHC.Exts (Int#)
import Helpers (first)

{-# NOINLINE forward #-}
forward :: Int# -> Int# -> Int#
forward x y = first y x

{-# NOINLINE constant #-}
constant :: Int# -> Int#
constant x = first 42# x
