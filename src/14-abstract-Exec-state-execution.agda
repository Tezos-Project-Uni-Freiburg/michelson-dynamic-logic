
module 14-abstract-Exec-state-execution where

open import 01-Types
open import 02-Functions-Interpretations
open import 03-concrete-execution
open import 11-abstract-representation-and-weakening
open import 12-abstract-execution-accessories-and-weakening 
open import 13-abstract-Prog-state-execution

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


------------------------- getting Context additions from successor Prog-state -----------

-- when symb. executing αExecState that contains a not yet terminated αProg-state αρ
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
∃⊎Γ++ (αstate αen end r`VM s`VM Φ) = [ [] ] , refl , tt
∃⊎Γ++ (αstate αen (enf `AMOUNT ; prg) r`VM s`VM Φ) = [ [] ] , refl , tt
∃⊎Γ++ (αstate αen (enf `BALANCE ; prg) r`VM s`VM Φ) = [ [] ] , refl , tt
∃⊎Γ++ (αstate αen (enf (`CONTRACT P) ; prg) (adr∈ ∷ r`VM) s`VM Φ)
  = [ [ option (contract P) ] ] , refl , tt
∃⊎Γ++ (αstate αen (fct (D1 {result = result} f) ; prg) r`VM s`VM Φ) = [ [ result ] ] , refl , tt
∃⊎Γ++ (αstate αen (fct (Dm (`UNPAIR {t1} {t2})) ; prg) (p∈ ∷ r`VM) s`VM Φ)
  = [ [ t1 / t2 ] ] , refl , tt
∃⊎Γ++ (αstate αen (fct (Dm `SWAP) ; prg) (x∈ ∷ y∈ ∷ r`VM) s`VM Φ) = [ [] ] , refl , tt
∃⊎Γ++ (αstate αen (fct (Dm `DUP) ; prg) (p∈ ∷ r`VM) s`VM Φ) = [ [] ] , refl , tt
∃⊎Γ++ (αstate αen (fct (`PUSH P x) ; prg) r`VM s`VM Φ) = [ expandΓ P x ] , refl , tt
∃⊎Γ++ (αstate αen (DROP ; prg) (v∈ ∷ r`VM) s`VM Φ) = [ [] ] , refl , tt
∃⊎Γ++ (αstate αen (ITER x ; prg) (l∈ ∷ r`VM) s`VM Φ) = [ [] ] , refl , tt
∃⊎Γ++ (αstate αen (DIP n x ; prg) r`VM s`VM Φ) = [ [] ] , refl , tt
∃⊎Γ++ (αstate αen (IF-NONE {t = t} x x₁ ; prg) (o∈ ∷ r`VM) s`VM Φ)
  = [ [] / [ t ] ] , refl , refl , tt
∃⊎Γ++ (αstate αen (ITER' {ty} x ∙ prg) r`VM (l∈ ∷ s`VM) Φ)
  = [ [] / [ ty / list ty ] ] , refl , refl , tt
∃⊎Γ++ (αstate αen (DIP' top ∙ prg) r`VM s`VM Φ) = [ [] ] , refl , tt

------------------------- Execution state execution :D ----------------------------------

-- other than what's mentioned above regarding ∃⊎Γ++ for application of αprog-step,
-- αexec-step is either very similar to exec-step when handling a terminated contract ex.
-- or it unfortunately cannot mimic its behaviour at all when dealing with
-- pending operations. These can only be executed if lots of additional information is
-- present, encoded in elements of Φ, and without assuming such information
-- pending operations cannot be symb. executed and we only to a rather meaningless
-- disjunction since it's all that can be done at this level.
-- the next modules will deal with this shortcoming.
αexec-step : ∀ {Γ} → αExecState Γ → ⊎ExecState
αexec-step {Γ} (αexc
  αccounts
  (inj₁ (αpr {ss = s} self sender (αstate
    (αenv _ cadr sadr blc∈ amn∈) end (no,ns∈ ∷ [M]) [M] Φ))) pending)
  with cadr ≟ₙ sadr
... | yes _ = [ [ list ops / s // Γ ]
              , αexc (βset cadr (αupdsrg (wkC self) 1∈) (wkβ αccounts))
                     (inj₂ [ 0∈ := func `CAR (2+ no,ns∈ ∷ [M])
                           / 1∈ := func `CDR (2+ no,ns∈ ∷ [M]) // wkΦ Φ ])
                     (wkp pending ++ [ 0∈ , cadr ]) ]
... | no  _ = [ [ list ops / s / mutez // Γ ]
              , αexc (βset cadr (αupdate (wkC self) (wk∈ blc∈) 1∈)
                     (βset sadr (αupdblc (wkC sender)         2∈) (wkβ αccounts)))
                     (inj₂ [ 0∈ := func `CAR (wk∈ no,ns∈ ∷ [M])
                           / 1∈ := func `CDR (wk∈ no,ns∈ ∷ [M])
                           / 2∈ := wk⊢ (αContract.balance sender ∸ₘ amn∈) // wkΦ Φ ])
                     (wkp pending ++ [ 0∈ , cadr ]) ]
αexec-step {Γ} (αexc
  αccounts
  (inj₁ (αpr {ss = s} self sender αρ)) pending)
  = build⊎σ (αprog-step αρ) (∃⊎Γ++ αρ)
  where
    build⊎σ : (⊎ρ` : ⊎Prog-state [ pair (list ops) s ] [])
            → ∃[ ⊎Γ++ ] (mod⊎wk ⊎Γ++ Γ (get⊎Γ ⊎ρ`)) → ⊎ExecState
    build⊎σ [] ([] , tt) = []
    build⊎σ [ Γ` , αρ` // ⊎Γ`,αρ` ] ([ Γ++ // ⊎Γ++ ] , refl , ++Γ≡⊎Γ`)
      = [  Γ` , αexc (wkβ αccounts)
                     (inj₁ (αpr (wkC self) (wkC sender) αρ`))
                     (wkp pending)
        // build⊎σ ⊎Γ`,αρ` (⊎Γ++ , ++Γ≡⊎Γ`) ]
αexec-step ασ@(αexc αccounts (inj₂ Φ) []) = [ _ , ασ ]
αexec-step {Γ} ασ@(αexc αccounts (inj₂ Φ) [ lops∈Γ , adr // pending ])
  with αccounts adr
... | nothing = [ Γ , record ασ{ pending = pending } ]
... | just (p , _ , sender)
  = [ Γ , αexc αccounts (inj₂ [ lops∈Γ := func (`NIL _) [M] // Φ ]) pending
    / [ ops / list ops // Γ ]
    , αexc (wkβ αccounts) (inj₂ [ 2+ lops∈Γ := func `CONS (0∈ ∷ 1∈ ∷ [M]) // wkΦ Φ ])
           (wkp [ lops∈Γ , adr // pending ]) ]

-- these are again for convenience ...
⊎exec-step : ⊎ExecState → ⊎ExecState
⊎exec-step [] = []
⊎exec-step [ _ , ασ // ⊎σ ] = αexec-step ασ ++ ⊎exec-step ⊎σ

⊎exec-exec : ℕ → ⊎ExecState → ℕ × ⊎ExecState
⊎exec-exec zero starved = zero , starved
⊎exec-exec gas [] = gas , []
⊎exec-exec gas [ _ , ασ@(αexc _ (inj₂ _) _) // ⊎σ ] with ⊎exec-exec gas ⊎σ
... | rest , ⊎σ* = rest , [ _ , ασ // ⊎σ* ]
⊎exec-exec (suc gas) ⊎σ = ⊎exec-exec gas (⊎exec-step ⊎σ)

infixl 3 _app-exec_
_app-exec_ : ⊎ExecState → ℕ → ⊎ExecState
⊎σ app-exec gas = proj₂ (⊎exec-exec gas ⊎σ)

