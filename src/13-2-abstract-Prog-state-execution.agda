
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

--! Abstract >

------------------------- Program state execution ---------------------------------------

-- this is explained in the thesis (section 4.3) and works mostly very similar to the
-- concrete prog-step except for branching instructions that create disjunctions
--! ProgStep
αprog-step : ∀ {Γ ro} → αProg-state Γ ro → ⊎Prog-state ro

αprog-step terminal@(state αen end αst Φ) = [ -, terminal ]

αprog-step α@(state αen (enf `AMOUNT  ; prg) αst Φ)
  = [ -, record α{ prg = prg ; stk = Environment.amount  αen ∷ αst } ]
αprog-step α@(state αen (enf `BALANCE ; prg) αst Φ)
  = [ -, record α{ prg = prg ; stk = Environment.balance αen ∷ αst } ]
αprog-step {Γ} (state αen (enf (`CONTRACT P) ; prg) (adr∈ ∷ αst) Φ)
  = [ [ option (contract P) // Γ ]
    , (state (wkαE αen) (wkSP prg) (0∈ ∷ wkM αst) (wkΦ Φ)) ]

--! ProgStepDOne
αprog-step {Γ} (state αen (fct (D1 {result = result} f) ; prg) αst Φ)
  = [ (result ∷ Γ)
    , state (wkαE αen) (wkSP prg) (0∈ ∷ wkM (H.rest αst)) 
            (0∈ := wk⊢ (func f (H.front αst)) ∷ wkΦ Φ ) ]

--! ProgStepUNPAIR
αprog-step {Γ} (state αen (fct (Dm (`UNPAIR {t1} {t2})) ; prg) (p∈ ∷ αst) Φ)
  = [ (t1 ∷ t2 ∷ Γ)
    , state (wkαE αen) (wkSP prg) (0∈ ∷ 1∈ ∷ wkM αst) 
            ( 0∈ := func `CAR [ wk∈ p∈ ] ∷ 1∈ := func `CDR [ wk∈ p∈ ] ∷  wkΦ Φ ) ]

--! ProgStepSWAP
αprog-step α@(state αen (fct (Dm `SWAP) ; prg) (x∈ ∷ y∈ ∷ αst) Φ)
  = [ -, record α{ prg = prg ; stk = y∈ ∷ x∈ ∷ αst } ]

αprog-step α@(state αen (fct (Dm `DUP)  ; prg) (x∈      ∷ αst) Φ)
  = [ -, record α{ prg = prg ; stk = x∈ ∷ x∈ ∷ αst } ]

--! ProgStepPUSH
αprog-step {Γ} (state αen (fct (`PUSH P x) ; prg) αst Φ)
  = [ (expandΓ P x ++ Γ)
    , state (wkαE αen) (wkSP prg) ((∈wk (0∈exΓ P)) ∷ wkM αst)
            (Φwk (unfold P x) ++ wkΦ Φ) ]

αprog-step α@(state αen (DROP   ; prg) (v∈ ∷ αst) Φ)
  = [ -, record α{ prg = prg ; stk = αst } ]

αprog-step α@(state {ri} αen (DIP n x ; prg) αst Φ)
  = [ -, record α{ prg = x ;∙ mpush (H.take n αst) prg ; stk = H.drop n αst } ]

--! ProgStepIFNONE
αprog-step {Γ} (state αen (IF-NONE {t = t} thn els ; prg) (o∈ ∷ αst) Φ)
  =  [ Γ        , state αen         (thn ;∙ prg)       αst (o∈ := func (`NONE t) [] ∷ Φ) 
     ⨾ (t ∷ Γ)  , state (wkαE αen)  (els ;∙ wkSP prg)  (0∈ ∷ wkM αst)
                        (wk∈ o∈ := func `SOME [ 0∈ ] ∷ wkΦ Φ) ]

--! ProgStepITER
αprog-step {Γ} α@(state αen (ITER {ty} ip ; prg) (l∈ ∷ αst) Φ)
  =  [ -, record α{ prg = prg ; stk = αst ; Φ = [ l∈ := func (`NIL ty) [M] // Φ ] } ]
  ++ [ (ty ∷ list ty ∷ Γ)
     , state (wkαE αen) (ip ;∙ (MPUSH1 1∈ ∙ ITER ip ; wkSP prg)) (0∈ ∷ wkM αst)
             [ 2+ l∈ := func `CONS (0∈ ∷ 1∈ ∷ [M]) // wkΦ Φ ] ]

--! ProgStepMPUSH
αprog-step α@(state αen (MPUSH1 x∈ ∙ prg) αst Φ)
  = [ -, record α{ prg = prg ; stk = x∈ ∷ αst } ]


-- these functions are again for conveniently executing several steps
⊎prog-step : ∀ {ro} → ⊎Prog-state ro → ⊎Prog-state ro
⊎prog-step states = concatMap (αprog-step ∘ proj₂) states
-- ⊎prog-step [] = []
-- ⊎prog-step [ _ , αρ // ⊎ρ ] = αprog-step αρ ++ ⊎prog-step ⊎ρ

⊎prog-exec : ∀ {ro} → ℕ → ⊎Prog-state ro → ℕ × ⊎Prog-state ro
⊎prog-exec zero starved = zero , starved
⊎prog-exec (suc gas) [] = suc gas , []
⊎prog-exec (suc gas) [ _ , αend@(state αen end αst Φ) // ⊎ρ ] with ⊎prog-exec gas ⊎ρ
... | rem-gas , ⊎end = rem-gas , [ _ , αend // ⊎end ]
⊎prog-exec (suc gas) ⊎ρ = ⊎prog-exec gas (⊎prog-step ⊎ρ)

