import Prelude hiding (iterate)
-- ^ so we can implement iterate it ourselves as an example

import Data.List (iterate', nub)

-- We need names for our variables.
-- In class these are secretly indices, which we don't mention at all.
-- Instead we just say x0, x1, x2,.. and we informally use any variable we like,
-- by taking proper care to pick the right variables, when working with examples.
--
-- Here we will refer to a variable directly by its index

type Name = Int

-- Our regular languages will be implemented based on section 1.8.1
-- from the notes found here - https://learn.fmi.uni-sofia.bg/pluginfile.php/219405/mod_forum/attachment/48554/sep.pdf?forcedownload=1
--
-- Our gramar:
-- τ ::= ∅ | ε | ai · Xj | τ1 + τ2 .
--
-- Which we can translate almost directly to a datatype:
-- * ∅ is Empty - The empty language
-- * ε is Epsilon - The language with one word in it.
-- * ai · Xj is Cons - Putting a character in front of a variable.
--   Note that while the language over there works over an arbitrary alphabet,
--   we will use Haskell's Char for simplicity, noting that we can make it polymorphic,
--   if we so desire.
-- * τ1 + τ2 is Plus - Either the first language or the second.
data RegLang
  = Empty
  | Epsilon
  | Append Char Name
  | Plus RegLang RegLang

-- We will now implement the denotational semantics given in the notes,
-- using Haskell as our "host" language - in the notes hte "host" language is set theory.

-- In set theory a language is simply a set of words.
-- In Haskell a "word" is a String (a list of Chars - just like we do in maths)
-- And a "set" will be a list - so a language is a list of strings.
-- We might have duplicates but it will not matter for our purposes.
-- It can also easily be remedied.
type Language = [String]

-- Now we will translate the "semantic brackets" from the notes,
-- again almost directly, by taking into account our Set -> List translation
--
-- The "semantic brackets" from the notes correspond to a function which
-- when given a term gives back a function from Language^n to Language.
-- In order to have arbitrarily large ns we will use a list instead of an n-tuple.
-- We can actually enforce that the length is n but this is fancy haskell type trickery,
-- and is irrelevant right now.
--
-- In order to define a function we match on all the cases of the datatype.
interpret :: RegLang -> [Language] -> Language
interpret Empty _ = [] -- the empty language has no words
interpret Epsilon _ = [""] -- epsilon has one word - the empty word
interpret (Append c i) langs = map (c:) $ langs !! i
  -- ^ Here the i index comes into effect - we need to get xi from our input n-tuple
  -- in other words we need to index our list of langs
  -- Afterwards we interpret Append as we usually do in maths, but translated to lists:
  -- We prepend c to each of the words in our lang
interpret (Plus l1 l2) langs =
  interpret l1 langs `interleave` interpret l2 langs
  -- ^ We interpret "Plus" as interleaving of two lists, after we first interpret each RegLang individually.
  -- By interleaving I mean: interleave [1,1,1] [2,2,2] == [1,2,1,2,1,2]
  -- We could just as well use list append, but this is a more "fair" way to implement set union.

-- Interleave implementation
interleave :: [a] -> [a] -> [a]
interleave [] ys = ys
interleave xs [] = xs
interleave (x:xs) ys = x : interleave ys xs

-- A "system" will again mean just a list of RegLangs.
type System = [RegLang]

-- We will use the definition given in the notes almost directly.
-- First we need to define the operator "x" from the notes.
-- I will call this "pointwise application" of a list of functions to a value.
pointwise :: [a -> b] -> a -> [b]
pointwise fs x = map (\f -> f x) fs

-- The bottom value in the products of Scott domains of regular languages
-- is an n-tuple of empty languages.
-- We need a function to generate such a thing.
bottomRegLangN :: System -> [Language]
bottomRegLangN taus = replicate (length taus) []

-- iterate will implement a part of our least fixed point operator.
-- We want to "infinitely" iterate a function over an initial value
-- Since we have finite time, unlike in math, we will instead return
-- a list of the results, so that we can use only as much as we need
--
-- The result of (iterate f x) is [x, f x, f (f x), f (f (f x))...]
-- These are the finite approximations of our operator.
iterate :: (a -> a) -> a -> [a]
iterate f x = x : iterate f (f x)

-- Then we can directly write down what denotation semantics is defined as,
-- using the notes. We will not be choosing a language to be our "main language",
-- as it's more convenient when programming, and we can easily implement
-- what is done in the notes (choosing the first language to be the main language) by doing map head.
denotSystem :: System -> Language
denotSystem taus =
  let interps :: [[Language] -> Language]
      interps = map interpret taus
      -- ^ We take all the interpretations of our input RegLangs,
      -- getting a list of functions (their interpretations)
   in nub
    -- ^ remove duplicate strings
    -- this isn't really needed, but it
    -- * makes usage prettier
    -- * it corresponds better to our mathematical implementation, which uses sets
    $ concatMap head
    -- ^ in the end we take all the first elements of our approximations,
    -- as that's where our "main" language is.
    $ cutOffIfFixed
    -- ^ since we might be given a finite language sometimes
    -- we will take our infinite list and try to cut it off
    -- at a point when two neighbouring elements are equal
    -- (i.e. we've reached a point where x == f x
    -- or a fixed point of f in other words)
    $ iterate' (pointwise interps)
    -- ^ iterate' is *the same* as iterate, except it
    -- evaluates its argument each time (for efficiency)
    $ bottomRegLangN taus
    -- ^ we generate a list (n-tuple) of "enough" bottoms (empty language)
    -- where "enough" is  how many RegLangs we were given (because that's how many we need)

-- The implementation of "cutting off the list when two neighbouring elements are equal"
cutOffIfFixed :: Eq a => [a] -> [a]
cutOffIfFixed [] = error "shouldn't be calling me with finite lists"
cutOffIfFixed (x:y:xs) = if x == y then [x] else x : cutOffIfFixed (y:xs)

--------- Some examples to play with.

-- a
a = [Append 'a' 1, Epsilon]

-- (ab)*
abStar = [Plus Epsilon (Append 'a' 1), Append 'b' 0]

-- (a|b)*
aOrbStar = [Plus Epsilon (Plus (Append 'a' 0) (Append 'b' 0))]
