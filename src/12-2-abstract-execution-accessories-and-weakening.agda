
module 12-2-abstract-execution-accessories-and-weakening where

open import 01-Types
open import 02-Functions-Interpretations
open import 03-2-concrete-execution
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

open import Data.List.Relation.Unary.All renaming (map to amap)
open import Data.List.Relation.Unary.Any hiding (map)
open import Data.List.Membership.Propositional using (_∈_)

open import Function using (_∘_)

--! Abstract >

--! AMode
AMode : Context → MODE
AMode Γ = record { 𝓜 = _∈ Γ
                 ; 𝓕 = List (Formula Γ)
                 ; 𝓖 = List (Formula Γ) ⊎ List (Formula Γ)
                 }

Abstract : ∀ {a}{A : Set a} → (MODE → A) → Context → A
Abstract F Γ = F (AMode Γ)

pattern AFail Φ   = Fail (inj₁ Φ)
pattern APanic Φ  = Fail (inj₂ Φ)


{-
  this module introduces all the necessary constructs for symbolic execuction
  they are all abstract counterparts of the similarly named constructs for concrete
  execution from the 03-concrete-execution module, and since they mostly work exactly
  the same as for concrete execution, we only mention the differences here.
  one difference that applies to all of them is that these are parameterized
  by the context. Most values are replaced by variables of the same type, except for
  blockchain addresses.
  We chose `NOT to abstract blockchain addresses, since this would only lead to a model
  where `ANY transfer operation would have had to be considered to be directed at `ANY
  contract, unless both addresses happen to be given concrete values in that case.
  This would not only make the implementation of an abstract blockchain a lot harder,
  the expected gain in expressiveness of such a `DL is also highly debatable since
  symbolically executing these operations would lead to possibly as many disjunctions
  as there are contracts saved on the blockchain.
  Hence, whenever the concrete constructs would save account address values, so do
  their abstract counterparts
-}
------------------------- Contract and blockchain ---------------------------------------

αContract : Context → Type → Type → Set
αContract = Abstract Contract


βlockchain : Context → Set
βlockchain = Abstract Blockchain

------------------------- Environment and Execution states ------------------------------

αEnvironment : Context → Set
αEnvironment = Abstract Environment

-- since the stacks are only lists of variables that don't contain any concrete values
-- a new field is needed to express any additional knowlegde of the self state
-- in a conjunction of formulas (represented as lists)
αProg-state : Context → Stack → Set
αProg-state = Abstract Prog-state

-- record αProg-state Γ (ro so : Stack) : Set where
--   constructor αstate
--   field
--     {ri si} : Stack
--     αen : αEnvironment Γ
--     prg : ShadowProg ri si ro so
--     rVM : Match Γ ri
--     sVM : Match Γ si
--     Φ   : List (Formula Γ)

αPrgRunning : Context → Set
αPrgRunning = Abstract PrgRunning

-- record αPrgRunning Γ : Set where
--   constructor αpr
--   field
--     {pp ss x y} : Type
--     self  : αContract Γ pp ss
--     sender   : αContract Γ x y
--     αρ       : αProg-state Γ [ pair (list ops) ss ] []

-- all relevant information is in the Φ field of a currently running contract execution
-- when that execution terminates, we cannot just drop αPrgRunning like in the concrete
-- setting we would loose all that information.
-- so instead of MPstate of type Maybe, αExecState holds either αPrgRunning or Φ
-- to save execution results
αTransaction : Context → Set
αTransaction = Abstract Transaction

-- record αPending (Γ : Context) : Set where
--   constructor _,_
--   field
--     αpops : list ops ∈ Γ
--     αsender : ⟦ addr ⟧
    
αExecState : Context → Set
αExecState = Abstract ExecState

-- record αExecState Γ : Set where
--   constructor αexc
--   field
--     αccounts : βlockchain Γ
--     αρ⊎Φ     : αPrgRunning Γ ⊎ List (Formula Γ)
--     pending  : List (αTransaction Γ)

Abstract* : (MODE → Set) → Set
Abstract* F = List (∃[ Γ ] Abstract F Γ)

-- symbolic execution may lead to disjunctions
--! UProgState
⊎Prog-state : Stack → Set
⊎Prog-state ro = List (∃[ Γ ] αProg-state Γ ro)

-- ⊎Prog-state ro = Abstract* λ M → Prog-state M ro

⊎ExecState : Set
-- ⊎ExecState = List (∃[ Γ ] αExecState Γ)
⊎ExecState = Abstract* ExecState

------------------------- updating Contract and blockchain ------------------------------

αupd-balance = upd-balance
αupd-storage = upd-storage
αupdate = update
-- αupd-balance = λ {Γ} {p} {s} (αc : αContract Γ p s) b∈Γ     → record αc{ balance = b∈Γ }
-- αupd-storage = λ {Γ} {p} {s} (αc : αContract Γ p s)     s∈Γ → record αc{ storage = s∈Γ }
-- αupdate = λ {Γ} {p} {s} (αc : αContract Γ p s) b∈Γ s∈Γ → record αc{ balance = b∈Γ ; storage = s∈Γ }
βset = set
-- βset : ∀ {p s Γ} → ⟦ addr ⟧ → αContract Γ p s → βlockchain Γ → βlockchain Γ
-- βset adr c βl a
--   with a ≟ₙ adr
-- ... | yes refl = just (_ , _ , c)
-- ... | no  ¬adr = βl a

β∅ : ∀ {Γ} → βlockchain Γ
β∅ = ∅

------------------------- weakenings ----------------------------------------------------
-- here are some basic weakening functions

wkSI : ∀ {Γ` Γ ri ro} → ShadowInst{_∈ Γ} ri ro → ShadowInst{_∈ (Γ` ++ Γ)} ri ro
-- wkSI (DIP' front) = DIP' front
-- wkSI (ITER' x) = ITER' x
-- wkSI (`MPUSH x) = `MPUSH (amap wk∈ x)
wkSI (MPUSH1 x) = MPUSH1 (wk∈ x)

wkSP : ∀ {Γ` Γ ri ro} → ShadowProg{_∈ Γ} ri ro → ShadowProg{_∈ (Γ` ++ Γ)} ri ro
wkSP end = end
wkSP (x ; sp) =  x ; wkSP sp
wkSP (x ∙ sp) = wkSI x ∙ wkSP sp

wkC : ∀ {Γ` Γ p s} → αContract Γ p s → αContract (Γ` ++ Γ) p s
wkC (ctr P S balance storage program) = ctr P S (wk∈ balance) (wk∈ storage) program

wk`MC : ∀ {Γ` Γ} → Maybe (∃[ p ] ∃[ s ] αContract        Γ  p s)
                → Maybe (∃[ p ] ∃[ s ] αContract (Γ` ++ Γ) p s)
wk`MC (just (p , s , αc)) = just (p , s , wkC αc)
wk`MC nothing = nothing

wkβ : ∀ {Γ` Γ} → βlockchain Γ → βlockchain (Γ` ++ Γ)
wkβ βl adr = wk`MC (βl adr)

wkαE : ∀ {Γ` Γ} → αEnvironment Γ → αEnvironment (Γ` ++ Γ)
wkαE (env      αccounts  self sender      balance       amount)
  =   env (wkβ αccounts) self sender (wk∈ balance) (wk∈ amount)

wktr : ∀ {Γ` Γ : Context} → αTransaction Γ → αTransaction (Γ` ++ Γ)
wktr (pops , psender) = wk∈ pops , psender


wkp : ∀ {Γ` Γ : Context} → List (αTransaction        Γ)
                         → List (αTransaction (Γ` ++ Γ))
wkp pending = map wktr pending

