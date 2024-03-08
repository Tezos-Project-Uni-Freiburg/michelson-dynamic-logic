
module 13-abstract-Prog-state-execution where

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
αprog-step : ∀ {Γ ro so} → αProg-state Γ {ro} {so} → ⊎Prog-state {ro} {so}

αprog-step terminal@(αstate αen end rVM sVM Φ) = [ _ , terminal ]

αprog-step α@(αstate αen (enf AMOUNT  ; prg) rVM sVM Φ)
  = [ _ , record α{ prg = prg ; rVM = αEnvironment.amount  αen ∷ rVM } ]
αprog-step α@(αstate αen (enf BALANCE ; prg) rVM sVM Φ)
  = [ _ , record α{ prg = prg ; rVM = αEnvironment.balance αen ∷ rVM } ]
αprog-step {Γ} (αstate αen (enf (CONTRACT P) ; prg) (adr∈ ∷ rVM) sVM Φ)
  = [ [ option (contract P) // Γ ]
    , (αstate (wkαE αen) prg (0∈ ∷ wkM rVM) (wkM sVM) (wkΦ Φ)) ]

αprog-step {Γ} (αstate αen (fct (D1 {result} f) ; prg) rVM sVM Φ)
  = [ [ result // Γ ]
    , (αstate (wkαE αen) prg (0∈ ∷ wkM (Mbot rVM)) (wkM sVM)
              [ 0∈ := wk⊢ (func f (Mtop rVM)) // wkΦ Φ ]) ]

αprog-step {Γ} (αstate αen (fct (Dm (UNPAIR {t1} {t2})) ; prg) (p∈ ∷ rVM) sVM Φ)
  = [ [ t1 / t2 // Γ ]
    , (αstate (wkαE αen) prg (0∈ ∷ 1∈ ∷ wkM rVM) (wkM sVM)
              [ 0∈ := wk⊢ (func CAR (p∈ ∷ [M]))
              / 1∈ := wk⊢ (func CDR (p∈ ∷ [M])) // wkΦ Φ ]) ]
αprog-step α@(αstate αen (fct (Dm SWAP) ; prg) (x∈ ∷ y∈ ∷ rVM) sVM Φ)
  = [ _ , record α{ prg = prg ; rVM = y∈ ∷ x∈ ∷ rVM } ]
αprog-step α@(αstate αen (fct (Dm DUP)  ; prg) (x∈      ∷ rVM) sVM Φ)
  = [ _ , record α{ prg = prg ; rVM = x∈ ∷ x∈ ∷ rVM } ]

αprog-step {Γ} (αstate αen (fct (PUSH P x) ; prg) rVM sVM Φ)
  = [ (expandΓ P x ++ Γ)
    , (αstate (wkαE αen) prg ((∈wk (0∈exΓ P)) ∷ wkM rVM) (wkM sVM)
              (Φwk (unfold P x) ++ wkΦ Φ)) ]

αprog-step α@(αstate αen (DROP   ; prg) (v∈ ∷ rVM) sVM Φ)
  = [ _ , record α{ prg = prg ; rVM = rVM } ]
αprog-step α@(αstate {ri} αen (DIP n x ; prg) rVM sVM Φ)
  = [ _ , record α{ prg = x ;∙ DIP' (take n ri) ∙ prg ; rVM = dropM n rVM
                                        ; sVM = takeM n rVM +M+ sVM } ]
αprog-step α@(αstate αen (DIP' top ∙ prg) rVM sVM Φ)
  = [ _ , record α{ prg = prg ; rVM = Mtop sVM +M+ rVM ; sVM = Mbot sVM } ]

αprog-step {Γ} α@(αstate αen (IF-NONE {ty} thn els ; prg) (o∈ ∷ rVM) sVM Φ)
  = [ _ , record α{ prg = thn ;∙ prg ; rVM = rVM
                  ; Φ = [ o∈ := func (NONE ty) [M] // Φ ] }
    / [ ty // Γ ]
    , αstate (wkαE αen) (els ;∙ prg) (0∈ ∷ wkM rVM) (wkM sVM)
             [ there o∈ := func SOME (0∈ ∷ [M]) // wkΦ Φ ] ]

αprog-step α@(αstate αen (ITER x ; prg) (l∈ ∷ rVM) sVM Φ)
  = [ _ , record α{ prg = ITER' x ∙ prg ; rVM = rVM ; sVM = l∈ ∷ sVM } ]

αprog-step {Γ} α@(αstate αen (ITER' {ty} x ∙ prg) rVM (l∈ ∷ sVM) Φ)
  = [ _ , record α{ prg = prg ; sVM = sVM ; Φ = [ l∈ := func (NIL ty) [M] // Φ ] }
    / [ ty / list ty // Γ ]
    , αstate (wkαE αen) (x ;∙ ITER' x ∙ prg) (0∈ ∷ wkM rVM) (1∈ ∷ wkM sVM)
             [ 2+ l∈ := func CONS (0∈ ∷ 1∈ ∷ [M]) // wkΦ Φ ] ]

-- these functions are again for conveniently executing several steps
⊎prog-step : ∀ {ro so} → ⊎Prog-state {ro} {so} → ⊎Prog-state {ro} {so}
⊎prog-step [] = []
⊎prog-step [ _ , αρ // ⊎ρ ] = αprog-step αρ ++ ⊎prog-step ⊎ρ

⊎prog-exec : ∀ {ro so} → ℕ → ⊎Prog-state {ro} {so} → ℕ × ⊎Prog-state {ro} {so}
⊎prog-exec zero starved = zero , starved
⊎prog-exec gas [] = gas , []
⊎prog-exec gas [ _ , αend@(αstate αen end rVM sVM Φ) // ⊎ρ ] with ⊎prog-exec gas ⊎ρ
... | rem-gas , ⊎end = rem-gas , [ _ , αend // ⊎end ]
⊎prog-exec (suc gas) ⊎ρ = ⊎prog-exec gas (⊎prog-step ⊎ρ)

