
module 14-2-abstract-Exec-state-execution where

open import 01-Types
open import 02-Functions-Interpretations
open import 03-2-concrete-execution
open import 11-abstract-representation-and-weakening
open import 12-2-abstract-execution-accessories-and-weakening 
open import 13-2-abstract-Prog-state-execution

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality.Core

open import Data.Nat renaming (_≟_ to _≟ₙ_) hiding (_/_)
open import Data.List.Base hiding ([_]; unfold)
open import Data.Maybe.Base hiding (map)
open import Data.Product hiding (map)
open import Data.Sum hiding ([_,_]; map)
open import Data.Unit
open import Data.Empty

open import Data.List.Relation.Unary.All using (All; _∷_; [])
open import Data.List.Relation.Unary.Any hiding (map)
open import Data.List.Membership.Propositional using (_∈_)

open import Function using (_∘_)

------------------------- getting Context additions from successor Prog-state -----------

-- when symb. executing αExec-state that contains a not yet terminated αProg-state αρ
-- this will again be executed by evaluating αprog-step αρ
-- however this will now yield a disjunction of abstract program states unlike in the
-- concrete setting, and we have to employ ∃⊎Γ++ which proofes for every possible
-- abstract program state that all resulting abstract state disjunctions from αprog-step
-- will be parameterized by an extension of the original context

get⊎Γ : ∀ {ro so} → ⊎Prog-state ro so → List Context
get⊎Γ ⊎ρ = map proj₁ ⊎ρ

mod⊎wk : List Context → Context → List Context → Set
mod⊎wk []              Γ [] = ⊤
mod⊎wk [ Γ++ // ⊎Γ++ ] Γ [ Γ` // ⊎Γ` ] = Γ++ ++ Γ ≡ Γ` × mod⊎wk ⊎Γ++ Γ ⊎Γ`
mod⊎wk _ _ _ = ⊥

∃⊎Γ++ : ∀ {Γ ro so} αρ → ∃[ ⊎Γ++ ] mod⊎wk ⊎Γ++ Γ (get⊎Γ (αprog-step {Γ} {ro} {so} αρ))
∃⊎Γ++ (state αen end rVM sVM Φ) = [ [] ] , refl , tt
∃⊎Γ++ (state αen (enf AMOUNT ; prg) rVM sVM Φ) = [ [] ] , refl , tt
∃⊎Γ++ (state αen (enf BALANCE ; prg) rVM sVM Φ) = [ [] ] , refl , tt
∃⊎Γ++ (state αen (enf (CONTRACT P) ; prg) (adr∈ ∷ rVM) sVM Φ)
  = [ [ option (contract P) ] ] , refl , tt
∃⊎Γ++ (state αen (fct (D1 {result = result} f) ; prg) rVM sVM Φ) = [ [ result ] ] , refl , tt
∃⊎Γ++ (state αen (fct (Dm (UNPAIR {t1} {t2})) ; prg) (p∈ ∷ rVM) sVM Φ)
  = [ [ t1 / t2 ] ] , refl , tt
∃⊎Γ++ (state αen (fct (Dm SWAP) ; prg) (x∈ ∷ y∈ ∷ rVM) sVM Φ) = [ [] ] , refl , tt
∃⊎Γ++ (state αen (fct (Dm DUP) ; prg) (p∈ ∷ rVM) sVM Φ) = [ [] ] , refl , tt
∃⊎Γ++ (state αen (fct (PUSH P x) ; prg) rVM sVM Φ) = [ expandΓ P x ] , refl , tt
∃⊎Γ++ (state αen (DROP ; prg) (v∈ ∷ rVM) sVM Φ) = [ [] ] , refl , tt
∃⊎Γ++ (state αen (ITER x ; prg) (l∈ ∷ rVM) sVM Φ) = [ [] ] , refl , tt
∃⊎Γ++ (state αen (DIP n x ; prg) rVM sVM Φ) = [ [] ] , refl , tt
∃⊎Γ++ (state αen (IF-NONE {t = t} x x₁ ; prg) (o∈ ∷ rVM) sVM Φ)
  = [ [] / [ t ] ] , refl , refl , tt
∃⊎Γ++ (state αen (ITER' {ty} x ∙ prg) rVM (l∈ ∷ sVM) Φ)
  = [ [] / [ ty / list ty ] ] , refl , refl , tt
∃⊎Γ++ (state αen (DIP' top ∙ prg) rVM sVM Φ) = [ [] ] , refl , tt

------------------------- Execution state execution :D ----------------------------------

-- other than what's mentioned above regarding ∃⊎Γ++ for application of αprog-step,
-- αexec-step is either very similar to exec-step when handling a terminated contract ex.
-- or it unfortunately cannot mimic its behaviour at all when dealing with
-- pending operations. These can only be executed if lots of additional information is
-- present, encoded in elements of Φ, and without assuming such information
-- pending operations cannot be symb. executed and we only to a rather meaningless
-- disjunction since it's all that can be done at this level.
-- the next modules will deal with this shortcoming.
αexec-step : ∀ {Γ} → αExec-state Γ → ⊎Exec-state
αexec-step {Γ} (exc
  αccounts
  (inj₁ (pr {ss = s} current sender (state
    (env _ cadr sadr blc∈ amn∈) end (no,ns∈ ∷ [M]) [M] Φ))) pending)
  with cadr ≟ₙ sadr
... | yes _ = [ [ list ops / s // Γ ]
              , exc (βset cadr (αupdsrg (wkC current) 1∈) (wkβ αccounts))
                     (inj₂ [ 0∈ := func CAR (2+ no,ns∈ ∷ [M])
                           / 1∈ := func CDR (2+ no,ns∈ ∷ [M]) // wkΦ Φ ])
                     (wkp pending ++ [ 0∈ , cadr ]) ]
... | no  _ = [ [ list ops / s / mutez // Γ ]
              , exc (βset cadr (αupdate (wkC current) (wk∈ blc∈) 1∈)
                     (βset sadr (αupdblc (wkC sender)         2∈) (wkβ αccounts)))
                     (inj₂ [ 0∈ := func CAR (wk∈ no,ns∈ ∷ [M])
                           / 1∈ := func CDR (wk∈ no,ns∈ ∷ [M])
                           / 2∈ := wk⊢ (Contract.balance sender ∸ₘ amn∈) // wkΦ Φ ])
                     (wkp pending ++ [ 0∈ , cadr ]) ]
αexec-step {Γ} (exc
  αccounts
  (inj₁ (pr {ss = s} current sender αρ)) pending)
  = build⊎σ (αprog-step αρ) (∃⊎Γ++ αρ)
  where
    build⊎σ : (⊎ρ` : ⊎Prog-state [ pair (list ops) s ] [])
            → ∃[ ⊎Γ++ ] (mod⊎wk ⊎Γ++ Γ (get⊎Γ ⊎ρ`)) → ⊎Exec-state
    build⊎σ [] ([] , tt) = []
    build⊎σ [ Γ` , αρ` // ⊎Γ`,αρ` ] ([ Γ++ // ⊎Γ++ ] , refl , ++Γ≡⊎Γ`)
      = [  Γ` , exc (wkβ αccounts)
                     (inj₁ (pr (wkC current) (wkC sender) αρ`))
                     (wkp pending)
        // build⊎σ ⊎Γ`,αρ` (⊎Γ++ , ++Γ≡⊎Γ`) ]
αexec-step ασ@(exc αccounts (inj₂ Φ) []) = [ _ , ασ ]
αexec-step {Γ} ασ@(exc αccounts (inj₂ Φ) [ lops∈Γ , adr // pending ])
  with αccounts adr
... | nothing = [ Γ , record ασ{ pending = pending } ]
... | just (p , _ , sender)
  = [ Γ , exc αccounts (inj₂ [ lops∈Γ := func (NIL _) [M] // Φ ]) pending
    / [ ops / list ops // Γ ]
    , exc (wkβ αccounts) (inj₂ [ 2+ lops∈Γ := func CONS (0∈ ∷ 1∈ ∷ [M]) // wkΦ Φ ])
           (wkp [ lops∈Γ , adr // pending ]) ]

-- these are again for convenience ...
⊎exec-step : ⊎Exec-state → ⊎Exec-state
⊎exec-step states = concatMap (αexec-step ∘ proj₂) states
-- ⊎exec-step [] = []
-- ⊎exec-step [ _ , ασ // ⊎σ ] = αexec-step ασ ++ ⊎exec-step ⊎σ

⊎exec-exec : ℕ → ⊎Exec-state → ℕ × ⊎Exec-state
⊎exec-exec zero starved = zero , starved
⊎exec-exec gas [] = gas , []
⊎exec-exec gas [ _ , ασ@(exc _ (inj₂ _) _) // ⊎σ ] with ⊎exec-exec gas ⊎σ
... | rest , ⊎σ* = rest , [ _ , ασ // ⊎σ* ]
⊎exec-exec (suc gas) ⊎σ = ⊎exec-exec gas (⊎exec-step ⊎σ)

infixl 3 _app-exec_
_app-exec_ : ⊎Exec-state → ℕ → ⊎Exec-state
⊎σ app-exec gas = proj₂ (⊎exec-exec gas ⊎σ)

