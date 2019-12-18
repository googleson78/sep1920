## `RegLang.hs`

Синтактичното дърво на граматиката на регулярните изрази е `RegLang`, в началото на файла.

Функцията `denotSystem` реализира денотационната семантика на
система (списък) от регулярни изрази (`RegLang`-ове).

Най-долу във файла има няколко пример с които може да го изпробвате:
```haskell
> ghci RegLang.hs
GHCi, version 8.6.5: http://www.haskell.org/ghc/  :? for help
Loaded GHCi configuration from /home/googleson78/.ghci
[1 of 1] Compiling Main             ( RegLang.hs, interpreted )
Ok, one module loaded.
> take 10 $ denotSystem a
["a"]
> take 10 $ denotSystem abStar
["","ab","abab","ababab","abababab","ababababab","abababababab","ababababababab","abababababababab","ababababababababab"]
> take 10 $ denotSystem aOrbStar
["","a","b","aa","ba","ab","bb","aaa","baa","aba"]
```
