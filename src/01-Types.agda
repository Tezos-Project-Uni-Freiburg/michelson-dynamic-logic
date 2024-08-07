
module 01-Types where

open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Binary.Definitions
open import Relation.Nullary

open import Function using (_∘_)

open import Data.Nat using (ℕ)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Product using (_×_; _,_)
open import Data.Unit using (⊤; tt)


{-
  Type restrictions
    contract          : `NOT pushable/storable (but passable/duplicable)
    operation         : `ONLY!!!! duplicable (`NO push/store/pass-as-param)
    list/pair/option  : depends on subtypes
-}

--! Types >

-- syntax of Michelson types

data Type : Set
variable
  t t₁ t₂ : Type

data
--!! Passable
  Passable : Type → Set

--! Type {
data BaseType : Set where
  `unit `nat `addr `mutez : BaseType

data Type where
  operation    : Type
  base         : BaseType → Type
  pair         : Type → Type → Type
  list option  : Type → Type
  contract     : ∀ {t} → Passable t → Type
--! }

--! PassableDefinition
data Passable where
  base      : ∀ bt → Passable (base bt)
  contract  : ∀ P  → Passable (contract {t} P)
  pair      : Passable t₁ → Passable t₂ → Passable (pair t₁ t₂)
  list      : Passable t                → Passable (list t)
  option    : Passable t                → Passable (option t)

--! Pushable
data Pushable : Type → Set where
  base    : ∀ bt → Pushable (base bt)
  pair    : Pushable t₁ → Pushable t₂ → Pushable (pair t₁ t₂)
  list    : Pushable t                 → Pushable (list t)
  option  : Pushable t                 → Pushable (option t)

--! Storable
Storable = Pushable -- this is only coincidentally true for the small subset of implemented types

variable
  bt : BaseType

--! Patterns
pattern unit   = base `unit
pattern nat    = base `nat
pattern addr   = base `addr
pattern mutez  = base `mutez

pattern ops = operation

-- semantics of Michelson types

--! Semantics {
Addr   = ℕ  -- blockchain addresses
Mutez  = ℕ  -- Tezos currency
data Operation : Set

⟦_⟧ : Type → Set
⟦ unit ⟧        = ⊤
⟦ nat ⟧         = ℕ
⟦ addr ⟧        = Addr
⟦ mutez ⟧       = Mutez
⟦ operation ⟧   = Operation
⟦ pair t₁ t₂ ⟧  = ⟦ t₁ ⟧ × ⟦ t₂ ⟧
⟦ list t ⟧      = List  ⟦ t ⟧
⟦ option t ⟧    = Maybe ⟦ t ⟧
⟦ contract P ⟧  = Addr

data Operation where
  transfer-tokens : ∀ {P : Passable t}
    → ⟦ t ⟧ → ⟦ mutez ⟧ → ⟦ contract P ⟧
    → Operation
--! }


--! Data
data Data : Type → Set where
  `DUnit   : Data unit
  `DNat    : ℕ → Data nat
  `DAddr   : Addr → Data addr
  `DMutez  : Mutez → Data mutez
  `DPair   : Data t₁ → Data t₂ → Data (pair t₁ t₂)
  `DNone   : ∀ {t} → Pushable t → Data (option t)
  `DSome   : Data t → Data (option t)
  `DNil    : ∀ {t} →  Pushable t → Data (list t)
  `DCons   : Data t → Data (list t) → Data (list t)

--! DataSemantics
⟦_⟧ᴰ : Data t → ⟦ t ⟧
⟦ `DUnit ⟧ᴰ        = tt
⟦ `DNat x ⟧ᴰ       = x
⟦ `DAddr x ⟧ᴰ      = x
⟦ `DMutez x ⟧ᴰ     = x
⟦ `DPair d₁ d₂ ⟧ᴰ  = ⟦ d₁ ⟧ᴰ , ⟦ d₂ ⟧ᴰ
⟦ `DNone t ⟧ᴰ      = nothing
⟦ `DSome d ⟧ᴰ      = just ⟦ d ⟧ᴰ
⟦ `DNil t ⟧ᴰ       = []
⟦ `DCons d₁ d₂ ⟧ᴰ  = ⟦ d₁ ⟧ᴰ ∷ ⟦ d₂ ⟧ᴰ

data-pushable : ∀ {t} → Data t → Pushable t
data-pushable `DUnit = unit
data-pushable (`DNat x) = nat
data-pushable (`DAddr x) = addr
data-pushable (`DMutez x) = mutez
data-pushable (`DPair d₁ d₂) = pair (data-pushable d₁) (data-pushable d₂)
data-pushable (`DNone P) = option P
data-pushable (`DSome d) = option (data-pushable d)
data-pushable (`DNil P) = list P
data-pushable (`DCons d₁ d₂) = data-pushable d₂

--------------------------------------------------------------------------------
Passable? : (t : Type) → Dec (Passable t)
Passable? ops = no (λ())
Passable? (base x) = yes (base x)
Passable? (pair t₁ t₂) with Passable? t₁ | Passable? t₂
... | no ¬P₁ | P₂     = no (λ{ (pair x₁ x₂) → ¬P₁ x₁})
... | yes P₁ | no ¬P₂ =  no (λ{ (pair x₁ x₂) → ¬P₂ x₂})
... | yes P₁ | yes P₂ = yes (pair P₁ P₂)
Passable? (list t) with Passable? t
... | no ¬P = no (λ{ (list x) → ¬P x})
... | yes P = yes (list P)
Passable? (option t) with Passable? t
... | no ¬P = no (λ{ (option x) → ¬P x})
... | yes P = yes (option P)
Passable? (contract P) = yes (contract P)

--------------------------------------------------------------------------------
Storable? : (t : Type) → Dec (Storable t)
Storable? ops = no (λ())
Storable? (base x) = yes (base x)
Storable? (pair t₁ t₂) with Storable? t₁ | Storable? t₂
... | no ¬P₁ | P₂     = no (λ{ (pair x₁ x₂) → ¬P₁ x₁})
... | yes P₁ | no ¬P₂ =  no (λ{ (pair x₁ x₂) → ¬P₂ x₂})
... | yes P₁ | yes P₂ = yes (pair P₁ P₂)
Storable? (list t) with Storable? t
... | no ¬P = no (λ{ (list x) → ¬P x})
... | yes P = yes (list P)
Storable? (option t) with Storable? t
... | no ¬P = no (λ{ (option x) → ¬P x})
... | yes P = yes (option P)
Storable? (contract P) = no (λ())

--------------------------------------------------------------------------------
Passable-irrelevant : ∀ {t} → (P₁ P₂ : Passable t) → P₁ ≡ P₂
Passable-irrelevant (base bt) (base .bt) = refl
Passable-irrelevant (contract P₁) (contract .P₁) = refl
Passable-irrelevant (pair P₁ P₂) (pair P₃ P₄) = cong₂ pair (Passable-irrelevant P₁ P₃) (Passable-irrelevant P₂ P₄)
Passable-irrelevant (list P₁) (list P₂) = cong list (Passable-irrelevant P₁ P₂)
Passable-irrelevant (option P₁) (option P₂) = cong option (Passable-irrelevant P₁ P₂)

--------------------------------------------------------------------------------
{- DecidableEquality for Types 
  necessary for execution of some instructions and operations
  they way it's programmed here is a little annoying,
  i was wondering whether there was some Agda magic to do it more efficiently,
  but it works fine and most cases can automatically be filled in by Agda,
  so it was left as is
-}
_≟`_ : DecidableEquality BaseType
`unit  ≟` `unit  = yes refl
`unit  ≟` `nat   = no (λ ())
`unit  ≟` `mutez = no (λ ())
`unit  ≟` `addr  = no (λ ())
`nat   ≟` `unit  = no (λ ())
`nat   ≟` `nat   = yes refl
`nat   ≟` `mutez = no (λ ())
`nat   ≟` `addr  = no (λ ())
`mutez ≟` `unit  = no (λ ())
`mutez ≟` `nat   = no (λ ())
`mutez ≟` `mutez = yes refl
`mutez ≟` `addr  = no (λ ())
`addr  ≟` `unit  = no (λ ())
`addr  ≟` `nat   = no (λ ())
`addr  ≟` `mutez = no (λ ())
`addr  ≟` `addr  = yes refl

_≟ₚ_ : ∀ {t} → DecidableEquality (Passable t)
base bt ≟ₚ base .bt = yes refl
contract pt₁ ≟ₚ contract .pt₁ = yes refl
pair pt₁ pt₃ ≟ₚ pair pt₂ pt₄ with pt₁ ≟ₚ pt₂ | pt₃ ≟ₚ pt₄
... | no ¬p | whate = no λ{ refl → ¬p refl}
... | whate | no ¬p = no λ{ refl → ¬p refl}
... | yes refl | yes refl = yes refl
list pt₁ ≟ₚ list pt₂ with pt₁ ≟ₚ pt₂
... | no ¬p = no λ{ refl → ¬p refl}
... | yes refl = yes refl
option pt₁ ≟ₚ option pt₂ with pt₁ ≟ₚ pt₂
... | no ¬p = no λ{ refl → ¬p refl}
... | yes refl = yes refl

_≟_ : DecidableEquality Type
ops ≟ ops = yes refl
ops ≟ base x = no (λ ())
ops ≟ pair t₂ t₃ = no (λ ())
ops ≟ list t₂ = no (λ ())
ops ≟ option t₂ = no (λ ())
ops ≟ contract t₂ = no (λ ())
base b₁ ≟ ops = no (λ ())
base b₁ ≟ base b₂ with b₁ ≟` b₂
... | no ¬p = no λ{ refl → ¬p refl}
... | yes refl = yes refl
base b₁ ≟ pair t₂ t₃ = no (λ ())
base b₁ ≟ list t₂ = no (λ ())
base b₁ ≟ option t₂ = no (λ ())
base b₁ ≟ contract t₂ = no (λ ())
pair t₁ t₃ ≟ ops = no (λ ())
pair t₁ t₃ ≟ base x = no (λ ())
pair t₁ t₃ ≟ pair t₂ t₄ with t₁ ≟ t₂ | t₃ ≟ t₄
... | no ¬p | whate = no λ{ refl → ¬p refl}
... | whate | no ¬p = no λ{ refl → ¬p refl}
... | yes refl | yes refl = yes refl
pair t₁ t₃ ≟ list t₂ = no (λ ())
pair t₁ t₃ ≟ option t₂ = no (λ ())
pair t₁ t₃ ≟ contract t₂ = no (λ ())
list t₁ ≟ ops = no (λ ())
list t₁ ≟ base x = no (λ ())
list t₁ ≟ pair t₂ t₃ = no (λ ())
list t₁ ≟ list t₂ with t₁ ≟ t₂
... | no ¬p = no λ{ refl → ¬p refl}
... | yes refl = yes refl
list t₁ ≟ option t₂ = no (λ ())
list t₁ ≟ contract t₂ = no (λ ())
option t₁ ≟ ops = no (λ ())
option t₁ ≟ base x = no (λ ())
option t₁ ≟ pair t₂ t₃ = no (λ ())
option t₁ ≟ list t₂ = no (λ ())
option t₁ ≟ option t₂ with t₁ ≟ t₂
... | no ¬p = no λ{ refl → ¬p refl}
... | yes refl = yes refl
option t₁ ≟ contract t₂ = no (λ ())
contract t₁ ≟ ops = no (λ ())
contract t₁ ≟ base x = no (λ ())
contract t₁ ≟ pair t₂ t₃ = no (λ ())
contract t₁ ≟ list t₂ = no (λ ())
contract t₁ ≟ option t₂ = no (λ ())
contract {t₁} pt₁ ≟ contract {t₂} pt₂ with t₁ ≟ t₂
... | no ¬p = no λ{ refl → ¬p refl}
... | yes refl with pt₁ ≟ₚ pt₂
... | no ¬p = no λ{ refl → ¬p refl}
... | yes refl = yes refl

--!! Stack
Stack = List Type

variable S Si So Se : Stack

