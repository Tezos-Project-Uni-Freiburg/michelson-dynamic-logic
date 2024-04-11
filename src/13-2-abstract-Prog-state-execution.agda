
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
αprog-step : ∀ {Γ ro} → αProg-state Γ ro → ⊎Prog-state ro

αprog-step terminal@(state αen end rVM Φ) = [ -, terminal ]

αprog-step α@(state αen (enf `AMOUNT  ; prg) rVM Φ)
  = [ -, record α{ prg = prg ; rSI = Environment.amount  αen ∷ rVM } ]
αprog-step α@(state αen (enf `BALANCE ; prg) rVM Φ)
  = [ -, record α{ prg = prg ; rSI = Environment.balance αen ∷ rVM } ]
αprog-step {Γ} (state αen (enf (`CONTRACT P) ; prg) (adr∈ ∷ rVM) Φ)
  = [ [ option (contract P) // Γ ]
    , (state (wkαE αen) (wkSP prg) (0∈ ∷ wkM rVM) (wkΦ Φ)) ]

αprog-step {Γ} (state αen (fct (D1 {result = result} f) ; prg) rVM Φ)
  = [ [ result // Γ ]
    , (state (wkαE αen) (wkSP prg) (0∈ ∷ wkM (H.bot rVM)) 
              [ 0∈ := wk⊢ (func f (H.top rVM)) // wkΦ Φ ]) ]

αprog-step {Γ} (state αen (fct (Dm (`UNPAIR {t1} {t2})) ; prg) (p∈ ∷ rVM) Φ)
  = [ [ t1 / t2 // Γ ]
    , (state (wkαE αen) (wkSP prg) (0∈ ∷ 1∈ ∷ wkM rVM) 
              [ 0∈ := wk⊢ (func `CAR (p∈ ∷ [M]))
              / 1∈ := wk⊢ (func `CDR (p∈ ∷ [M])) // wkΦ Φ ]) ]
αprog-step α@(state αen (fct (Dm `SWAP) ; prg) (x∈ ∷ y∈ ∷ rVM) Φ)
  = [ -, record α{ prg = prg ; rSI = y∈ ∷ x∈ ∷ rVM } ]
αprog-step α@(state αen (fct (Dm `DUP)  ; prg) (x∈      ∷ rVM) Φ)
  = [ -, record α{ prg = prg ; rSI = x∈ ∷ x∈ ∷ rVM } ]

αprog-step {Γ} (state αen (fct (`PUSH P x) ; prg) rVM Φ)
  = [ (expandΓ P x ++ Γ)
    , (state (wkαE αen) (wkSP prg) ((∈wk (0∈exΓ P)) ∷ wkM rVM)
              (Φwk (unfold P x) ++ wkΦ Φ)) ]

αprog-step α@(state αen (DROP   ; prg) (v∈ ∷ rVM) Φ)
  = [ -, record α{ prg = prg ; rSI = rVM } ]
-- αprog-step α@(state {ri} αen (DIP n x ; prg) rVM sVM Φ)
--   = [ -, record α{ prg = x ;∙ DIP' (take n ri) ∙ prg ; rSI = H.drop n rVM
--                                         ; s`SI = H.take n rVM H.++ sVM } ]
αprog-step α@(state {ri} αen (DIP n x ; prg) rVM Φ)
  = [ -, record α{ prg = x ;∙ mpush (H.take n rVM) prg ; rSI = H.drop n rVM } ]
-- αprog-step α@(state αen (DIP' top ∙ prg) rVM sVM Φ)
--   = [ -, record α{ prg = prg ; rSI = H.top sVM H.++ rVM ; s`SI = H.bot sVM } ]

αprog-step {Γ} α@(state αen (IF-NONE {t = t} thn els ; prg) (o∈ ∷ rVM) Φ)
  = [ -, record α{ prg = thn ;∙ prg ; rSI = rVM
                  ; Φ = [ o∈ := func (`NONE t) [M] // Φ ] }
    / [ t // Γ ]
    , state (wkαE αen) (els ;∙ wkSP prg) (0∈ ∷ wkM rVM)
             [ there o∈ := func `SOME (0∈ ∷ [M]) // wkΦ Φ ] ]

αprog-step {Γ} α@(state αen (ITER {ty} ip ; prg) (l∈ ∷ rVM) Φ)
  = [ -, record α{ prg = prg ; rSI = rVM ; Φ = [ l∈ := func (`NIL ty) [M] // Φ ] }
    / [ ty / list ty // Γ ]
    , state (wkαE αen) (ip ;∙ (MPUSH1 1∈ ∙ ITER ip ; wkSP prg)) (0∈ ∷ wkM rVM)
             [ 2+ l∈ := func `CONS (0∈ ∷ 1∈ ∷ [M]) // wkΦ Φ ] ]



-- αprog-step α@(state αen (ITER x ; prg) (l∈ ∷ rVM) sVM Φ)
--   = [ -, record α{ prg = ITER' x ∙ prg ; rSI = rVM ; s`SI = l∈ ∷ sVM } ]

-- αprog-step {Γ} α@(state αen (ITER' {ty} x ∙ prg) rVM (l∈ ∷ sVM) Φ)
--   = [ -, record α{ prg = prg ; s`SI = sVM ; Φ = [ l∈ := func (`NIL ty) [M] // Φ ] }
--     / [ ty / list ty // Γ ]
--     , state (wkαE αen) (x ;∙ ITER' x ∙ wkSP prg) (0∈ ∷ wkM rVM) (1∈ ∷ wkM sVM)
--              [ 2+ l∈ := func `CONS (0∈ ∷ 1∈ ∷ [M]) // wkΦ Φ ] ]

-- αprog-step α@(state αen (`MPUSH x ∙ prg) rVM sVM Φ)
--   = [ (-, (record α{ prg = prg ; rSI = x H.++ rVM })) ]

αprog-step α@(state αen (MPUSH1 x ∙ prg) rVM Φ)
  = [ (-, (record α{ prg = prg ; rSI = x ∷ rVM })) ]

-- these functions are again for conveniently executing several steps
⊎prog-step : ∀ {ro} → ⊎Prog-state ro → ⊎Prog-state ro
⊎prog-step states = concatMap (αprog-step ∘ proj₂) states
-- ⊎prog-step [] = []
-- ⊎prog-step [ _ , αρ // ⊎ρ ] = αprog-step αρ ++ ⊎prog-step ⊎ρ

⊎prog-exec : ∀ {ro} → ℕ → ⊎Prog-state ro → ℕ × ⊎Prog-state ro
⊎prog-exec zero starved = zero , starved
⊎prog-exec (suc gas) [] = suc gas , []
⊎prog-exec (suc gas) [ _ , αend@(state αen end rVM Φ) // ⊎ρ ] with ⊎prog-exec gas ⊎ρ
... | rem-gas , ⊎end = rem-gas , [ _ , αend // ⊎end ]
⊎prog-exec (suc gas) ⊎ρ = ⊎prog-exec gas (⊎prog-step ⊎ρ)

