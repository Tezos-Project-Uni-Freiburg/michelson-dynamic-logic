import Michelson-separate-minimal
open import Data.Nat

blubb = 42

module test where

  open Michelson-separate-minimal
  simple-01-program  = CRD ; NIL ops ; PAIR ; end
  simple-01-contract : Contract[p: unit
                                s: unit
                              prg: simple-01-program ]
  simple-01-contract = typechecked: id ∘ PAIR ∘ NIL ∘ CRD
  {-
  -}

