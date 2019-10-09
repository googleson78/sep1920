{-# OPTIONS --no-unicode #-}

module 01-intro-cont where

open import Lib.Maybe

open import 00-intro

-- Maybe induced order
-- this is actually already done in Lib.Maybe

-- maybe induced order is scott domain

-- X - a scott domain in which all chains stabilise
-- in X the LUB of a chain is the element at which it stabilises

-- Maybe Nat * Maybe Nat is a scott domain

-- (Maybe n) ^ k -> Maybe n
-- is a scott domain
-- [ _ -> _ ] syntax
-- [ A -> B ] == ( total functions (A -> B), f <= g == (a : A) f a <B= g a, bot == const (bot B) )
-- lub fs is h (a) = lub fs(a)
-- prove [ A -> B ] is a scott domain

-- A, B - scott domain
-- f : A -> B - monotone <->
-- (a1 a2 : A) (a1 <A= a2 -> f a1 <B= f a2)

-- [ A -M> B ] - same as before, but monotone, prove scott domain

-- forall i -> (c d : Chain) -> c i <= d i -> lub c <= lub d
-- prove that lub d is a ub for c

-- continuous functions
-- f : (A -> B) is continuous iff (c : Chain) -> f (lub c) == lub (\ i -> (f (c i)))
-- (and monotone*, but this might not be necessary*?)

-- again with [ A -C> B ], but with continuous

-- prove one direction of the continuous condition with only monotonicity

-- example of monotone non-continuous function
-- !nats with two ordered top elements and succ as a function
