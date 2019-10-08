module Lib.Sigma where

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

infixr 41 _><_
infixr 40 _*_
