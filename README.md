# MpEff: Efficient effect handlers based on Evidence Passing Semantics

Efficient effect handlers based on Evidence passing semantics. The implementation
is based on /"Generalized Evidence Passing for Effect Handlers"/, Ningning Xie and Daan Leijen, 2021 [(pdf)](https://www.microsoft.com/en-us/research/publication/generalized-evidence-passing-for-effect-handlers/),
The implementation is closely based on the [Ev.Eff](https://hackage.haskell.org/package/eveff) 
library described in detail in /"Effect Handlers in Haskell, Evidently"/, Ningning Xie and Daan Leijen, Haskell 2020 [(pdf)](https://www.microsoft.com/en-us/research/publication/effect-handlers-in-haskell-evidently).
The _Mp.Eff_ and _Ev.Eff_ libraries expose the exact same interface, but
the _Mp.Eff_ library can express full effect handler semantics, including non-scoped resumptions --
it is slightly slower though (see the 2021 paper for benchmarks and a detailed comparison).

Installation:

* First install [stack](https://docs.haskellstack.org)
* Build with `> stack build`

An example of defining and using a `Reader` effect:

```Haskell
{-# LANGUAGE  TypeOperators, FlexibleContexts, Rank2Types #-}
import Control.Mp.Eff

-- A @Reader@ effect definition with one operation @ask@ of type @()@ to @a@.
data Reader a e ans = Reader{ ask :: Op () a e ans }

greet :: (Reader String :? e) => Eff e String
greet = do s <- perform ask ()
           return ("hello " ++ s)

test :: String
test = runEff $
       handler (Reader{ ask = value "world" }) $  -- @:: Reader String () Int@
       do s <- greet                              -- executes in context @:: Eff (Reader String :* ()) Int@
          return (length s)
```

Enjoy,

Ningning Xie and Daan Leijen,  Mar 2021.
