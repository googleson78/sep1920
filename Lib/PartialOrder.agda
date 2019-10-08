{-# OPTIONS --no-unicode #-}

module Lib.PartialOrder where

open import Lib.Equality

-- things that are partial orders
-- technically we should probably require that the _<=_
-- operation return types with only one inhabitant
-- but it's not an issue for now (?)
-- we are probably going to need totality at some point though
record PartialOrder : Set1 where
  field
    Obj : Set
    _<=_ : Obj -> Obj -> Set
    <=-refl : {x : Obj} -> x <= x
    <=-trans : {x y z : Obj} -> x <= y -> y <= z -> x <= z
    <=-antisym : {x y : Obj} -> x <= y -> y <= x -> x == y
