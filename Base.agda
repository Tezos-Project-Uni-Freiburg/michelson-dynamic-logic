module Michelson-Base where

open import Data.Nat using (ℕ; _+_; _<?_; _≟_) public
open import Data.Unit using (⊤; tt) public
open import Data.Product using (_×_; proj₁; proj₂; _,_; Σ) public
open import Data.List using (List; []; _∷_; _++_; length) public
open import Data.Bool using (Bool; true; false) public
open import Data.Maybe using (Maybe; just; nothing) public
open import Data.Integer using (ℤ; +_) renaming (-[1+_] to -_) public

-- next 3 needed for decidable equality check
open import Relation.Binary using (DecidableEquality) public
open import Relation.Nullary public
open import Agda.Builtin.Equality public

infixr 5  _;;_
infixr 6  _;_

data Type : Set where
  ops nat unit bool int              : Type
  -- ops nat unit bool                  : Type
  pair            : (ty1 ty2 : Type) → Type
  list option     : (type : Type)    → Type


data Operation : Set where

⟦_⟧ : Type → Set
⟦ ops ⟧       = Operation
⟦ nat ⟧       = ℕ
⟦ unit ⟧      = ⊤
⟦ pair T T₁ ⟧ = ⟦ T ⟧ × ⟦ T₁ ⟧
⟦ list T ⟧    = List ⟦ T ⟧
⟦ bool ⟧      = Bool
⟦ option T ⟧  = Maybe ⟦ T ⟧
⟦ int ⟧       = ℤ


data Prog : Set

data Inst : Set where
  ADD CAR CDR PAIR CONS UNIT COMPARE LT SOME          :  Inst
  PUSH                : ∀ ty → ⟦ ty ⟧                 →  Inst
  NIL NONE            : ∀ (ty  : Type)                →  Inst
  ITER                : ∀ (prg : Prog)                →  Inst
  DIP                 : ∀ (n : ℕ) (prg : Prog)        →  Inst
  DROP DIG DUP DUG    : ∀ (n : ℕ)                     →  Inst
  IF IF-CONS IF-NONE  : ∀ (then else : Prog)          →  Inst

data Prog where
  end                     :  Prog
  _;_   : Inst → Prog     →  Prog

_;;_ : Prog → Prog → Prog
end ;; g = g
(i ; p) ;; g = i ; (p ;; g)

⟦_⇒_⟧ : List Type → Type → Set
⟦     [] ⇒ T ⟧ =              ⟦ T ⟧
⟦ A ∷ lT ⇒ T ⟧ = ⟦ A ⟧ → ⟦ lT ⇒ T ⟧

{-
is there a better way to do this:         _≟ₜ_ : DecidableEquality Type
  - less impos
  - _≟_ without ₜ
  - maybe somewhat shorter???
-}
_≟ₜ_ : DecidableEquality Type
ops  ≟ₜ ops  = yes refl
ops  ≟ₜ nat  = no (λ ())
ops  ≟ₜ unit = no (λ ())
ops  ≟ₜ pair ty2 ty3 = no (λ ())
ops  ≟ₜ list ty2 = no (λ ())
nat  ≟ₜ ops  = no (λ ())
nat  ≟ₜ nat  = yes refl
nat  ≟ₜ unit = no (λ ())
nat  ≟ₜ pair ty2 ty3 = no (λ ())
nat  ≟ₜ list ty2 = no (λ ())
unit ≟ₜ ops  = no (λ ())
unit ≟ₜ nat  = no (λ ())
unit ≟ₜ unit = yes refl
unit ≟ₜ pair ty2 ty3 = no (λ ())
unit ≟ₜ list ty2 = no (λ ())
pair ty1 ty3 ≟ₜ ops = no (λ ())
pair ty1 ty3 ≟ₜ nat = no (λ ())
pair ty1 ty3 ≟ₜ unit = no (λ ())
pair ty1 ty3 ≟ₜ pair ty2 ty4 with ty1 ≟ₜ ty2
... | no neq = no λ{ refl → neq refl}
... | yes refl with ty3 ≟ₜ ty4
... | no neq = no λ{ refl → neq refl}
... | yes refl = yes refl
pair ty1 ty3 ≟ₜ list ty2 = no (λ ())
list ty1 ≟ₜ ops = no (λ ())
list ty1 ≟ₜ nat = no (λ ())
list ty1 ≟ₜ unit = no (λ ())
list ty1 ≟ₜ pair ty2 ty3 = no (λ ())
list ty1 ≟ₜ list ty2 with ty1 ≟ₜ ty2
... | no neq = no λ{ refl → neq refl }
... | yes refl = yes refl
ops ≟ₜ bool = no (λ ())
ops ≟ₜ option ty2 = no (λ ())
nat ≟ₜ bool = no (λ ())
nat ≟ₜ option ty2 = no (λ ())
unit ≟ₜ bool = no (λ ())
unit ≟ₜ option ty2 = no (λ ())
bool ≟ₜ ops = no (λ ())
bool ≟ₜ nat = no (λ ())
bool ≟ₜ unit = no (λ ())
bool ≟ₜ bool = yes refl
bool ≟ₜ pair ty2 ty3 = no (λ ())
bool ≟ₜ list ty2 = no (λ ())
bool ≟ₜ option ty2 = no (λ ())
pair ty1 ty2 ≟ₜ bool = no (λ ())
pair ty1 ty2 ≟ₜ option ty3 = no (λ ())
list ty1 ≟ₜ bool = no (λ ())
list ty1 ≟ₜ option ty2 = no (λ ())
option ty1 ≟ₜ ops = no (λ ())
option ty1 ≟ₜ nat = no (λ ())
option ty1 ≟ₜ unit = no (λ ())
option ty1 ≟ₜ bool = no (λ ())
option ty1 ≟ₜ pair ty2 ty3 = no (λ ())
option ty1 ≟ₜ list ty2 = no (λ ())
option ty1 ≟ₜ option ty2 with ty1 ≟ₜ ty2
... | no neq = no λ{ refl → neq refl}
... | yes refl = yes refl
ops ≟ₜ int = no (λ ())
nat ≟ₜ int = no (λ ())
unit ≟ₜ int = no (λ ())
bool ≟ₜ int = no (λ ())
int ≟ₜ ops = no (λ ())
int ≟ₜ nat = no (λ ())
int ≟ₜ unit = no (λ ())
int ≟ₜ bool = no (λ ())
int ≟ₜ int = yes refl
int ≟ₜ pair ty2 ty3 = no (λ ())
int ≟ₜ list ty2 = no (λ ())
int ≟ₜ option ty2 = no (λ ())
pair ty1 ty2 ≟ₜ int = no (λ ())
list ty1 ≟ₜ int = no (λ ())
option ty1 ≟ₜ int = no (λ ())

Stack = List
fullStack = Stack (Σ Type ⟦_⟧)

{-  instructions needed for sort.tz:
  NONE
  SOME
  COMPARE
  LT
  IF
  IF_NONE
  IF_CONS
  SWAP ~> same as DIG 1 and DUG 1 !!
  DIG n
  DUG

  DUP (n?!)
-- also need new Type option!
-- also need new Type bool!
-- and int for COMPARE :D

... starting 1900 :D
... new types 1920 :D
... new inst's defined 1930 ... let's do typing ...
-}
