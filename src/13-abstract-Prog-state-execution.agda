
module 13-abstract-Prog-state-execution where

import 00-All-Utilities as H

open import 01-Types
open import 02-Functions-Interpretations
open import 03-concrete-execution
open import 11-abstract-representation-and-weakening
open import 12-abstract-execution-accessories-and-weakening 

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality.Core

open import Data.Nat renaming (_≟_ to _≟ₙ_) hiding (_/_)
open import Data.List.Base hiding ([_]; unfold)
open import Data.Maybe.Base hiding (map)
open import Data.Product hiding (map)
open import Data.Sum hiding ([_,_]; map)
open import Data.Unit
open import Data.Empty

open import Data.List.Relation.Unary.All
open import Data.List.Relation.Unary.Any hiding (map)
open import Data.List.Membership.Propositional using (_∈_)


------------------------- Program state execution ---------------------------------------

-- this is explained in the thesis (section 4.3) and works mostly very similar to the
-- concrete prog-step except for branching instructions that create disjunctions
αprog-step : ∀ {Γ ro so} → αProg-state Γ ro so → ⊎Prog-state ro so

αprog-step terminal@(αstate αen end r`VM s`VM Φ) = [ _ , terminal ]

αprog-step α@(αstate αen (enf `AMOUNT  ; prg) r`VM s`VM Φ)
  = [ _ , record α{ prg = prg ; r`VM = αEnvironment.amount  αen ∷ r`VM } ]
αprog-step α@(αstate αen (enf `BALANCE ; prg) r`VM s`VM Φ)
  = [ _ , record α{ prg = prg ; r`VM = αEnvironment.balance αen ∷ r`VM } ]
αprog-step {Γ} (αstate αen (enf (`CONTRACT P) ; prg) (adr∈ ∷ r`VM) s`VM Φ)
  = [ [ option (contract P) // Γ ]
    , (αstate (wkαE αen) prg (0∈ ∷ wkM r`VM) (wkM s`VM) (wkΦ Φ)) ]

αprog-step {Γ} (αstate αen (fct (D1 {result = result} f) ; prg) r`VM s`VM Φ)
  = [ [ result // Γ ]
    , (αstate (wkαE αen) prg (0∈ ∷ wkM (H.bot r`VM)) (wkM s`VM)
              [ 0∈ := wk⊢ (func f (H.top r`VM)) // wkΦ Φ ]) ]

αprog-step {Γ} (αstate αen (fct (Dm (`UNPAIR {t1} {t2})) ; prg) (p∈ ∷ r`VM) s`VM Φ)
  = [ [ t1 / t2 // Γ ]
    , (αstate (wkαE αen) prg (0∈ ∷ 1∈ ∷ wkM r`VM) (wkM s`VM)
              [ 0∈ := wk⊢ (func `CAR (p∈ ∷ [M]))
              / 1∈ := wk⊢ (func `CDR (p∈ ∷ [M])) // wkΦ Φ ]) ]
αprog-step α@(αstate αen (fct (Dm `SWAP) ; prg) (x∈ ∷ y∈ ∷ r`VM) s`VM Φ)
  = [ _ , record α{ prg = prg ; r`VM = y∈ ∷ x∈ ∷ r`VM } ]
αprog-step α@(αstate αen (fct (Dm `DUP)  ; prg) (x∈      ∷ r`VM) s`VM Φ)
  = [ _ , record α{ prg = prg ; r`VM = x∈ ∷ x∈ ∷ r`VM } ]

αprog-step {Γ} (αstate αen (fct (`PUSH P x) ; prg) r`VM s`VM Φ)
  = [ (expandΓ P x ++ Γ)
    , (αstate (wkαE αen) prg ((∈wk (0∈exΓ P)) ∷ wkM r`VM) (wkM s`VM)
              (Φwk (unfold P x) ++ wkΦ Φ)) ]

αprog-step α@(αstate αen (DROP   ; prg) (v∈ ∷ r`VM) s`VM Φ)
  = [ _ , record α{ prg = prg ; r`VM = r`VM } ]
αprog-step α@(αstate {ri} αen (DIP n x ; prg) r`VM s`VM Φ)
  = [ _ , record α{ prg = x ;∙ DIP' (take n ri) ∙ prg ; r`VM = H.drop n r`VM
                                        ; s`VM = H.take n r`VM H.++ s`VM } ]
αprog-step α@(αstate αen (DIP' top ∙ prg) r`VM s`VM Φ)
  = [ _ , record α{ prg = prg ; r`VM = H.top s`VM H.++ r`VM ; s`VM = H.bot s`VM } ]

αprog-step {Γ} α@(αstate αen (IF-NONE {t = t} thn els ; prg) (o∈ ∷ r`VM) s`VM Φ)
  = [ _ , record α{ prg = thn ;∙ prg ; r`VM = r`VM
                  ; Φ = [ o∈ := func (`NONE t) [M] // Φ ] }
    / [ t // Γ ]
    , αstate (wkαE αen) (els ;∙ prg) (0∈ ∷ wkM r`VM) (wkM s`VM)
             [ there o∈ := func `SOME (0∈ ∷ [M]) // wkΦ Φ ] ]

αprog-step α@(αstate αen (ITER x ; prg) (l∈ ∷ r`VM) s`VM Φ)
  = [ _ , record α{ prg = ITER' x ∙ prg ; r`VM = r`VM ; s`VM = l∈ ∷ s`VM } ]

αprog-step {Γ} α@(αstate αen (ITER' {ty} x ∙ prg) r`VM (l∈ ∷ s`VM) Φ)
  = [ _ , record α{ prg = prg ; s`VM = s`VM ; Φ = [ l∈ := func (`NIL ty) [M] // Φ ] }
    / [ ty / list ty // Γ ]
    , αstate (wkαE αen) (x ;∙ ITER' x ∙ prg) (0∈ ∷ wkM r`VM) (1∈ ∷ wkM s`VM)
             [ 2+ l∈ := func `CONS (0∈ ∷ 1∈ ∷ [M]) // wkΦ Φ ] ]

-- these functions are again for conveniently executing several steps
⊎prog-step : ∀ {ro so} → ⊎Prog-state ro so → ⊎Prog-state ro so
⊎prog-step [] = []
⊎prog-step [ _ , αρ // ⊎ρ ] = αprog-step αρ ++ ⊎prog-step ⊎ρ

⊎prog-exec : ∀ {ro so} → ℕ → ⊎Prog-state ro so → ℕ × ⊎Prog-state ro so
⊎prog-exec zero starved = zero , starved
⊎prog-exec gas [] = gas , []
⊎prog-exec gas [ _ , αend@(αstate αen end r`VM s`VM Φ) // ⊎ρ ] with ⊎prog-exec gas ⊎ρ
... | rem-gas , ⊎end = rem-gas , [ _ , αend // ⊎end ]
⊎prog-exec (suc gas) ⊎ρ = ⊎prog-exec gas (⊎prog-step ⊎ρ)

