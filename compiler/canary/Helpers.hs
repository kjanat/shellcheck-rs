{-# LANGUAGE MagicHash #-}
module Helpers (first) where

import GHC.Exts (Int#)

{-# NOINLINE first #-}
first :: Int# -> Int# -> Int#
first x _ = x
