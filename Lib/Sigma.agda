module Lib.Sigma where

open import Lib.Equality

-- a dependent pair - the type of the second element *can* depend on the value of the first
-- useful for "predicate holding things" - values that have a predicate attached to them
-- e.g. Nat >< \ p -> Prime p
-- would be a natural number, along with proof that it is prime
record _><_ (X : Set) (P : X -> Set) : Set where
  constructor _,_
  field
    fst : X
    snd : P fst

-- non-dependent pairs
_*_ : (X Y : Set) -> Set
X * Y = X >< \ _ -> Y

-- pairs that are elemwise equla are equal
-- not sure why I need this, since pairs are records but..
-- used in 00-intro currently
*-elemwise
  :  {X Y : Set} {u v : X * Y}
  -> _><_.fst u == _><_.fst v
  -> _><_.snd u == _><_.snd v
  -> u == v
*-elemwise refl refl = refl

infixr 41 _><_
infixr 40 _*_
