open import Michelson-separate-minimal

simple-01-program  = CRD ; NIL ops ; PAIR ; end
simple-01-contract : Contract[p: unit
                              s: unit
                            prg: simple-01-program ]
simple-01-contract = typechecked: id ∘ PAIR ∘ NIL ops ∘ CRD

{-
-}

