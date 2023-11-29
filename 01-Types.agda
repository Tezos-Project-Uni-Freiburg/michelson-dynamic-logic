
module 01-Types where

open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Binary.Definitions
open import Relation.Nullary

open import Function.Base

open import Data.Bool.Base
open import Data.Nat.Base
open import Data.List.Base hiding ([_])
open import Data.Maybe.Base
open import Data.Product


{-
  Type restrictions
    contract          : NOT pushable/storable (but passable/duplicatable)
    operation         : ONLY!!!! duplicatable (NO push/store/pass-as-param)
    list/pair/option  : depends on subtypes
-}

data BaseType : Set where
  unit nat mutez addr : BaseType

data Type : Set
data Passable : Type → Set

data Type where
  ops          :               Type
  base         : BaseType    → Type
  pair         : Type → Type → Type
  list option  : Type        → Type
  contract     : ∀ {ty} → Passable ty → Type

data Pushable : Type → Set where
  base   : ∀ bt → Pushable (base bt)
  pair   : ∀ {ty₁ ty₂} → Pushable ty₁ → Pushable ty₂ → Pushable (pair ty₁ ty₂)
  list   : ∀ {ty}      → Pushable ty                 → Pushable (list ty)
  option : ∀ {ty}      → Pushable ty                 → Pushable (option ty)

data Passable where
  base     : ∀ bt     → Passable (base bt)
  contract : ∀ {ty} P → Passable (contract {ty} P)
  pair     : ∀ {ty₁ ty₂} → Passable ty₁ → Passable ty₂ → Passable (pair ty₁ ty₂)
  list     : ∀ {ty}      → Passable ty                 → Passable (list ty)
  option   : ∀ {ty}      → Passable ty                 → Passable (option ty)

Storable = Pushable -- this is only coincidentally true for the small subset of implemented types

{- DecidableEquality for Types 
  necessary for execution of some instructions and operations
  they way it's programmed here is a little annoying,
  i was wondering whether there was some Agda magic to do it more efficiently,
  but it works fine and most cases can automatically be filled in by Agda,
  so it was left as is
-}
_≟`_ : DecidableEquality BaseType
unit  ≟` unit  = yes refl
unit  ≟` nat   = no (λ ())
unit  ≟` mutez = no (λ ())
unit  ≟` addr  = no (λ ())
nat   ≟` unit  = no (λ ())
nat   ≟` nat   = yes refl
nat   ≟` mutez = no (λ ())
nat   ≟` addr  = no (λ ())
mutez ≟` unit  = no (λ ())
mutez ≟` nat   = no (λ ())
mutez ≟` mutez = yes refl
mutez ≟` addr  = no (λ ())
addr  ≟` unit  = no (λ ())
addr  ≟` nat   = no (λ ())
addr  ≟` mutez = no (λ ())
addr  ≟` addr  = yes refl

_≟ₚ_ : ∀ {ty} → DecidableEquality (Passable ty)
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
ops ≟ pair ty₂ ty₃ = no (λ ())
ops ≟ list ty₂ = no (λ ())
ops ≟ option ty₂ = no (λ ())
ops ≟ contract ty₂ = no (λ ())
base b₁ ≟ ops = no (λ ())
base b₁ ≟ base b₂ with b₁ ≟` b₂
... | no ¬p = no λ{ refl → ¬p refl}
... | yes refl = yes refl
base b₁ ≟ pair ty₂ ty₃ = no (λ ())
base b₁ ≟ list ty₂ = no (λ ())
base b₁ ≟ option ty₂ = no (λ ())
base b₁ ≟ contract ty₂ = no (λ ())
pair ty₁ ty₃ ≟ ops = no (λ ())
pair ty₁ ty₃ ≟ base x = no (λ ())
pair ty₁ ty₃ ≟ pair ty₂ ty₄ with ty₁ ≟ ty₂ | ty₃ ≟ ty₄
... | no ¬p | whate = no λ{ refl → ¬p refl}
... | whate | no ¬p = no λ{ refl → ¬p refl}
... | yes refl | yes refl = yes refl
pair ty₁ ty₃ ≟ list ty₂ = no (λ ())
pair ty₁ ty₃ ≟ option ty₂ = no (λ ())
pair ty₁ ty₃ ≟ contract ty₂ = no (λ ())
list ty₁ ≟ ops = no (λ ())
list ty₁ ≟ base x = no (λ ())
list ty₁ ≟ pair ty₂ ty₃ = no (λ ())
list ty₁ ≟ list ty₂ with ty₁ ≟ ty₂
... | no ¬p = no λ{ refl → ¬p refl}
... | yes refl = yes refl
list ty₁ ≟ option ty₂ = no (λ ())
list ty₁ ≟ contract ty₂ = no (λ ())
option ty₁ ≟ ops = no (λ ())
option ty₁ ≟ base x = no (λ ())
option ty₁ ≟ pair ty₂ ty₃ = no (λ ())
option ty₁ ≟ list ty₂ = no (λ ())
option ty₁ ≟ option ty₂ with ty₁ ≟ ty₂
... | no ¬p = no λ{ refl → ¬p refl}
... | yes refl = yes refl
option ty₁ ≟ contract ty₂ = no (λ ())
contract ty₁ ≟ ops = no (λ ())
contract ty₁ ≟ base x = no (λ ())
contract ty₁ ≟ pair ty₂ ty₃ = no (λ ())
contract ty₁ ≟ list ty₂ = no (λ ())
contract ty₁ ≟ option ty₂ = no (λ ())
contract {ty₁} pt₁ ≟ contract {ty₂} pt₂ with ty₁ ≟ ty₂
... | no ¬p = no λ{ refl → ¬p refl}
... | yes refl with pt₁ ≟ₚ pt₂
... | no ¬p = no λ{ refl → ¬p refl}
... | yes refl = yes refl

Stack = List Type

