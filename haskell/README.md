## `RegLang.hs`

Синтактичното дърво на граматиката на регулярните изрази е имплементирана чрез типа `RegLang`, в началото на файла.

Функцията `denotSystem` реализира денотационната семантика на
система (списък) от регулярни изрази (`RegLang`-ове).

Най-долу във файла има няколко примера с които можем да го изпробваме:
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

## `ContextFree.hs`

Тъй като нещата съм почти 1 към 1 с `RegLang`, в този файл има много по-малко документация.

Синтактичното дърво на граматиката на безконтекстните езици е имплементирана чрез типа `ContextFree`, в началото на файла.

Функцията `denotSystem` реализира денотационната семантика на
система (списък) от термове от граматиката на безконтекстните езици (`ContextFree`-ове).

Най-долу във файла има пример с който можем да го изпробваме:
```haskell
> ghci ContextFree.hs
GHCi, version 8.6.5: http://www.haskell.org/ghc/  :? for help
Loaded GHCi configuration from /home/googleson78/.ghci
[1 of 2] Compiling RegLang          ( RegLang.hs, interpreted )
[2 of 2] Compiling ContextFree      ( ContextFree.hs, interpreted )
Ok, two modules loaded.
> take 10 $ denotSystem aNbN
["","ab","aabb","aaabbb","aaaabbbb","aaaaabbbbb","aaaaaabbbbbb","aaaaaaabbbbbbb","aaaaaaaabbbbbbbb","aaaaaaaaabbbbbbbbb"]
```
