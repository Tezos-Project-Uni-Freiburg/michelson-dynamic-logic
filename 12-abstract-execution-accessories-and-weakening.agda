
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

{-
  this module introduces all the necessary constructs for symbolic execuction
  they are all abstract counterparts of the similarly named constructs for concrete
  execution from the 03-concrete-execution module, and since they mostly work exactly
  the same as for concrete execution, we only mention the differences here.
  one difference that applies to all of them is that these are parameterized
  by the context. Most values are replaced by variables of the same type, except for
  blockchain addresses.
  We chose NOT to abstract blockchain addresses, since this would only lead to a model
  where ANY transfer operation would have had to be considered to be directed at ANY
  contract, unless both addresses happen to be given concrete values in that case.
  This would not only make the implementation of an abstract blockchain a lot harder,
  the expected gain in expressiveness of such a DL is also highly debatable since
  symbolically executing these operations would lead to possibly as many disjunctions
  as there are contracts saved on the blockchain.
  Hence, whenever the concrete constructs would save account address values, so do
  their abstract counterparts
-}
------------------------- Contract and blockchain ---------------------------------------

record αContract (Γ : Context) {p s : Type} : Set where
  constructor αctr
  field
    P : Passable p
    S : Storable s
    balance : mutez ∈ Γ
    storage : s ∈ Γ
    program : Program [ pair p s ] [ pair (list ops) s ]

βlockchain : Context → Set
βlockchain Γ = ⟦ addr ⟧ → Maybe (∃[ p ] ∃[ s ] αContract Γ {p} {s})

------------------------- Environment and Execution states ------------------------------

record αEnvironment (Γ : Context) : Set where
  constructor αenv
  field
    αccounts : βlockchain Γ
    current  : ⟦ addr ⟧
    sender   : ⟦ addr ⟧
    balance  : mutez ∈ Γ
    amount   : mutez ∈ Γ

-- since the stacks are only lists of variables that don't contain any concrete values
-- a new field is needed to express any additional knowlegde of the current state
-- in a conjunction of formulas (represented as lists)
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

-- all relevant information is in the Φ field of a currently running contract execution
-- when that execution terminates, we cannot just drop αPrg-running like in the concrete
-- setting we would loose all that information.
-- so instead of MPstate of type Maybe, αExec-state holds either αPrg-running or Φ
-- to save execution results
record αExec-state Γ : Set where
  constructor αexc
  field
    αccounts : βlockchain Γ
    αρ⊎Φ     : αPrg-running Γ ⊎ List (Formula Γ)
    pending  : List (list ops ∈ Γ × ⟦ addr ⟧)

-- symbolic execution may lead to disjunctions
⊎Prog-state = λ {ro} {so} → List (∃[ Γ ] αProg-state Γ {ro} {so})

⊎Exec-state = List (∃[ Γ ] αExec-state Γ)

------------------------- updating Contract and blockchain ------------------------------

αupdblc = λ {Γ} {p} {s} (αc : αContract Γ {p} {s}) b∈Γ     → record αc{ balance = b∈Γ }
αupdsrg = λ {Γ} {p} {s} (αc : αContract Γ {p} {s})     s∈Γ → record αc{ storage = s∈Γ }
αupdate = λ {Γ} {p} {s} (αc : αContract Γ {p} {s}) b∈Γ s∈Γ → record αc{ balance = b∈Γ
                                                                      ; storage = s∈Γ }
βset : ∀ {p s Γ} → ⟦ addr ⟧ → αContract Γ {p} {s} → βlockchain Γ → βlockchain Γ
βset adr c βl a
  with a ≟ₙ adr
... | yes refl = just (_ , _ , c)
... | no  ¬adr = βl a

β∅ : ∀ {Γ} → βlockchain Γ
β∅ adr = nothing

------------------------- weakenings ----------------------------------------------------
-- here are some basic weakening functions

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

wkp : ∀ {Γ` Γ : Context} → List (list ops ∈        Γ  × ⟦ addr ⟧)
                         → List (list ops ∈ (Γ` ++ Γ) × ⟦ addr ⟧)
wkp [] = []
wkp [ lops∈Γ , adr // pending ] = [ wk∈ lops∈Γ , adr // wkp pending ]

