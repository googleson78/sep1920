{-# OPTIONS --no-unicode #-}

module Lib.Zero where

-- empty type - impossible to construct - contradiction
data Zero : Set where

-- eliminator for the empty type (zero - naught - naughtElim - naughte)
naughte : {X : Set} -> Zero -> X
naughte ()
