
module 12-abstract-execution-accessories-and-weakening where

open import 01-Types
open import 02-Functions-Interpretations
open import 03-concrete-execution
open import 11-abstract-representation-and-weakening

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality.Core

open import Data.Nat renaming (_≟_ to _≟ₙ_) hiding (_/_)
open import Data.List.Base hiding ([_]; unfold)
open import Data.Maybe.Base hiding (map)
open import Data.Product hiding (map)
open import Data.Sum hiding ([_,_]; map)
open import Data.Unit
open import Data.Empty

open import Data.List.Relation.Unary.Any hiding (map)
open import Data.List.Membership.Propositional using (_∈_)


------------------------- Contract and blockchain ---------------------------------------

record αContract (Γ : Context) {p s : Type} : Set where
  constructor αctr
  field
    P : Passable p
    S : Storable s
    balance : base mutez ∈ Γ
    storage : s ∈ Γ
    program : Program [ pair p s ] [ pair (list ops) s ]

βlockchain : Context → Set
βlockchain Γ = ⟦ base addr ⟧ → Maybe (∃[ p ] ∃[ s ] αContract Γ {p} {s})

------------------------- Environment and Execution states ------------------------------

record αEnvironment (Γ : Context) : Set where
  constructor αenv
  field
    αccounts : βlockchain Γ
    current  : ⟦ base addr ⟧
    sender   : ⟦ base addr ⟧
    balance  : base mutez ∈ Γ
    amount   : base mutez ∈ Γ

record αProg-state Γ {ro so : Stack} : Set where
  constructor αstate
  field
    {ri si} : Stack
    αen : αEnvironment Γ
    prg : ShadowProg ri si ro so
    rVM : Match Γ ri
    sVM : Match Γ si
    Φ   : List (Formula Γ)

record αPrg-running Γ : Set where
  constructor αpr
  field
    {p s x y} : Type
    current  : αContract Γ {p} {s}
    sender   : αContract Γ {x} {y}
    αρ       : αProg-state Γ {[ pair (list ops) s ]} {[]}

record αExec-state Γ : Set where
  constructor αexc
  field
    αccounts : βlockchain Γ
    αρ⊎Φ     : αPrg-running Γ ⊎ List (Formula Γ)
    pending  : List (list ops ∈ Γ × ⟦ base addr ⟧)

⊎Prog-state = λ {ro} {so} → List (∃[ Γ ] αProg-state Γ {ro} {so})

-- new stuff :D
⊎Exec-state = List (∃[ Γ ] αExec-state Γ)

------------------------- updating Contract and blockchain ------------------------------

αupdblc = λ {Γ} {p} {s} (αc : αContract Γ {p} {s}) b∈Γ     → record αc{ balance = b∈Γ }
αupdsrg = λ {Γ} {p} {s} (αc : αContract Γ {p} {s})     s∈Γ → record αc{ storage = s∈Γ }
αupdate = λ {Γ} {p} {s} (αc : αContract Γ {p} {s}) b∈Γ s∈Γ → record αc{ balance = b∈Γ
                                                                      ; storage = s∈Γ }
βset : ∀ {p s Γ} → ⟦ base addr ⟧ → αContract Γ {p} {s} → βlockchain Γ → βlockchain Γ
βset adr c βl a
  with a ≟ₙ adr
... | yes refl = just (_ , _ , c)
... | no  ¬adr = βl a

β∅ : ∀ {Γ} → βlockchain Γ
β∅ adr = nothing

------------------------- weakenings ----------------------------------------------------

wkC : ∀ {Γ` Γ p s} → αContract Γ {p} {s} → αContract (Γ` ++ Γ) {p} {s}
wkC (αctr P S balance storage program) = αctr P S (wk∈ balance) (wk∈ storage) program

wkMC : ∀ {Γ` Γ} → Maybe (∃[ p ] ∃[ s ] αContract        Γ  {p} {s})
                → Maybe (∃[ p ] ∃[ s ] αContract (Γ` ++ Γ) {p} {s})
wkMC (just (p , s , αc)) = just (p , s , wkC αc)
wkMC nothing = nothing

wkβ : ∀ {Γ` Γ} → βlockchain Γ → βlockchain (Γ` ++ Γ)
wkβ βl adr = wkMC (βl adr)

wkαE : ∀ {Γ` Γ} → αEnvironment Γ → αEnvironment (Γ` ++ Γ)
wkαE (αenv      αccounts  current sender      balance       amount)
  =   αenv (wkβ αccounts) current sender (wk∈ balance) (wk∈ amount)

wkp : ∀ {Γ` Γ : Context} → List (list ops ∈        Γ  × ⟦ base addr ⟧)
                         → List (list ops ∈ (Γ` ++ Γ) × ⟦ base addr ⟧)
wkp [] = []
wkp [ lops∈Γ , adr // pending ] = [ wk∈ lops∈Γ , adr // wkp pending ]

