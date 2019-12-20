module ContextFree where

import Data.List (iterate', nub)
import RegLang (interleave, pointwise, cutOffIfFixed, bottomLangN)
-- ^ we will be reusing these

-- We could factor out more common parts out, but for
-- simplicity's sake we will not do so
-- (Also the RegLangs module would be harder to read if we
-- refactored out bits of it into another module)

-- For the context free languages the same things apply:
-- We will use integers for our variable "names"

type Name = Int

-- Direct translation of the grammar given in the notes, again:
--τ ::= X i | a j | ε | ∅ | τ 1 · τ 2 | (τ 1 + τ 2 ),
data ContextFree
  = Empty
  | Epsilon
  | Const Char
  | Var Int
  | Append ContextFree ContextFree
  | Plus ContextFree ContextFree

-- A Language is still a "set" (list) of Strings
type Language = [String]

-- We can even mostly copy-paster the interpretation.
interpret :: ContextFree -> [Language] -> Language
interpret Empty _ = []
interpret Epsilon _ = [""]
interpret (Const c) _ = [[c]]
-- ^ Const chars evaluate to a language with only one string in it - the Char itself
interpret (Var n) langs = langs !! n
-- ^ This time we have a separate case for variables, because we can do that
-- without accidentally creating context-dependent languages
interpret (Append cf1 cf2) langs =
  [str1 ++ str2 | str1 <- interpret cf1 langs, str2 <- interpret cf2 langs]
-- ^ we interpret each language individually, and then we implement
-- language appending as pairwise appending of strings
interpret (Plus l1 l2) langs =
  interpret l1 langs `interleave` interpret l2 langs
  -- ^ We interpret "Plus" as interleaving of two lists.
  -- By interleaving I mean: interleave [1,1,1] [2,2,2] == [1,2,1,2,1,2]
  -- We could just as well use list append, but this is a more "fair" way to implement set union.

type System = [ContextFree]

-- *exactly* the same thing as before,
-- but using the contextfree stuff instead
denotSystem :: System -> Language
denotSystem taus =
  let interps :: [[Language] -> Language]
      interps = map interpret taus
   in nub
    $ concatMap head
    $ cutOffIfFixed
    $ iterate' (pointwise interps)
    $ bottomLangN taus

--------- Some examples to play with.

-- a^nb^n - not regular
aNbN :: [ContextFree]
aNbN = [ Plus Epsilon (Append (Const 'a') (Var 1))
       , Append (Var 0) (Const 'b')
       ]

