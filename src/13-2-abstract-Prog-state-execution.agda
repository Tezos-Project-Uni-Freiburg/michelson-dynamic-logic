
module 13-2-abstract-Prog-state-execution where

import 00-All-Utilities as H

open import 01-Types
open import 02-Functions-Interpretations
open import 03-2-concrete-execution
open import 11-abstract-representation-and-weakening
open import 12-2-abstract-execution-accessories-and-weakening 

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

open import Function using (_∘_)


------------------------- Program state execution ---------------------------------------

-- this is explained in the thesis (section 4.3) and works mostly very similar to the
-- concrete prog-step except for branching instructions that create disjunctions
αprog-step : ∀ {Γ ro so} → αProg-state Γ ro so → ⊎Prog-state ro so

αprog-step terminal@(state αen end r`VM s`VM Φ) = [ -, terminal ]

αprog-step α@(state αen (enf `AMOUNT  ; prg) r`VM s`VM Φ)
  = [ -, record α{ prg = prg ; r`SI = Environment.amount  αen ∷ r`VM } ]
αprog-step α@(state αen (enf `BALANCE ; prg) r`VM s`VM Φ)
  = [ -, record α{ prg = prg ; r`SI = Environment.balance αen ∷ r`VM } ]
αprog-step {Γ} (state αen (enf (`CONTRACT P) ; prg) (adr∈ ∷ r`VM) s`VM Φ)
  = [ [ option (contract P) // Γ ]
    , (state (wkαE αen) prg (0∈ ∷ wkM r`VM) (wkM s`VM) (wkΦ Φ)) ]

αprog-step {Γ} (state αen (fct (D1 {result = result} f) ; prg) r`VM s`VM Φ)
  = [ [ result // Γ ]
    , (state (wkαE αen) prg (0∈ ∷ wkM (H.bot r`VM)) (wkM s`VM)
              [ 0∈ := wk⊢ (func f (H.top r`VM)) // wkΦ Φ ]) ]

αprog-step {Γ} (state αen (fct (Dm (`UNPAIR {t1} {t2})) ; prg) (p∈ ∷ r`VM) s`VM Φ)
  = [ [ t1 / t2 // Γ ]
    , (state (wkαE αen) prg (0∈ ∷ 1∈ ∷ wkM r`VM) (wkM s`VM)
              [ 0∈ := wk⊢ (func `CAR (p∈ ∷ [M]))
              / 1∈ := wk⊢ (func `CDR (p∈ ∷ [M])) // wkΦ Φ ]) ]
αprog-step α@(state αen (fct (Dm `SWAP) ; prg) (x∈ ∷ y∈ ∷ r`VM) s`VM Φ)
  = [ -, record α{ prg = prg ; r`SI = y∈ ∷ x∈ ∷ r`VM } ]
αprog-step α@(state αen (fct (Dm `DUP)  ; prg) (x∈      ∷ r`VM) s`VM Φ)
  = [ -, record α{ prg = prg ; r`SI = x∈ ∷ x∈ ∷ r`VM } ]

αprog-step {Γ} (state αen (fct (`PUSH P x) ; prg) r`VM s`VM Φ)
  = [ (expandΓ P x ++ Γ)
    , (state (wkαE αen) prg ((∈wk (0∈exΓ P)) ∷ wkM r`VM) (wkM s`VM)
              (Φwk (unfold P x) ++ wkΦ Φ)) ]

αprog-step α@(state αen (`DROP   ; prg) (v∈ ∷ r`VM) s`VM Φ)
  = [ -, record α{ prg = prg ; r`SI = r`VM } ]
αprog-step α@(state {ri} αen (`DIP n x ; prg) r`VM s`VM Φ)
  = [ -, record α{ prg = x ;∙ `DIP' (take n ri) ∙ prg ; r`SI = H.drop n r`VM
                                        ; s`SI = H.take n r`VM H.++ s`VM } ]
αprog-step α@(state αen (`DIP' top ∙ prg) r`VM s`VM Φ)
  = [ -, record α{ prg = prg ; r`SI = H.top s`VM H.++ r`VM ; s`SI = H.bot s`VM } ]

αprog-step {Γ} α@(state αen (`IF-NONE {t = t} thn els ; prg) (o∈ ∷ r`VM) s`VM Φ)
  = [ -, record α{ prg = thn ;∙ prg ; r`SI = r`VM
                  ; Φ = [ o∈ := func (`NONE t) [M] // Φ ] }
    / [ t // Γ ]
    , state (wkαE αen) (els ;∙ prg) (0∈ ∷ wkM r`VM) (wkM s`VM)
             [ there o∈ := func `SOME (0∈ ∷ [M]) // wkΦ Φ ] ]

αprog-step α@(state αen (`ITER x ; prg) (l∈ ∷ r`VM) s`VM Φ)
  = [ -, record α{ prg = `ITER' x ∙ prg ; r`SI = r`VM ; s`SI = l∈ ∷ s`VM } ]

αprog-step {Γ} α@(state αen (`ITER' {ty} x ∙ prg) r`VM (l∈ ∷ s`VM) Φ)
  = [ -, record α{ prg = prg ; s`SI = s`VM ; Φ = [ l∈ := func (`NIL ty) [M] // Φ ] }
    / [ ty / list ty // Γ ]
    , state (wkαE αen) (x ;∙ `ITER' x ∙ prg) (0∈ ∷ wkM r`VM) (1∈ ∷ wkM s`VM)
             [ 2+ l∈ := func `CONS (0∈ ∷ 1∈ ∷ [M]) // wkΦ Φ ] ]

-- these functions are again for conveniently executing several steps
⊎prog-step : ∀ {ro so} → ⊎Prog-state ro so → ⊎Prog-state ro so
⊎prog-step states = concatMap (αprog-step ∘ proj₂) states
-- ⊎prog-step [] = []
-- ⊎prog-step [ _ , αρ // ⊎ρ ] = αprog-step αρ ++ ⊎prog-step ⊎ρ

⊎prog-exec : ∀ {ro so} → ℕ → ⊎Prog-state ro so → ℕ × ⊎Prog-state ro so
⊎prog-exec zero starved = zero , starved
⊎prog-exec (suc gas) [] = suc gas , []
⊎prog-exec (suc gas) [ _ , αend@(state αen end r`VM s`VM Φ) // ⊎ρ ] with ⊎prog-exec gas ⊎ρ
... | rem-gas , ⊎end = rem-gas , [ _ , αend // ⊎end ]
⊎prog-exec (suc gas) ⊎ρ = ⊎prog-exec gas (⊎prog-step ⊎ρ)

