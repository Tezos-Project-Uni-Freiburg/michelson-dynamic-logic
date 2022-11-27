open import Data.Nat
open import Relation.Binary.PropositionalEquality


infix  3  _⊢_
infix  3  _↦_
infixr 4  _∷_
infix  6   ⊢_
infixl 2  _∶_
infix  3  _—→_


data Type : Set where
  ops  :                    Type
  nat  :                    Type
  unit :                    Type
  pair : (ty1 ty2 : Type) → Type
  list : (type : Type)    → Type

-- syntax of terms, Michelson doesn't have variables and therefore no context (i guess)

data ⊢_ : Type → Set where
  ⊢unit   :                                   ⊢ unit
  ⊢nat    : ∀ (n : ℕ)                      →  ⊢ nat
  ⊢pair   : ∀ {ty1 ty2}  →  ⊢ ty1 → ⊢ ty2  →  ⊢ pair ty1 ty2
  ⊢[]     : ∀ {ty}                         →  ⊢ list ty

data ⊢Stack : Set where
  []   :                               ⊢Stack
  _∷_  : ∀ {ty}  →  ⊢ ty → ⊢Stack  →   ⊢Stack

data _⊢_ : ⊢Stack → ⊢Stack → Set where
  ADD   : ∀ {⊢St n m}                                    →   ⊢nat n ∷ ⊢nat m ∷ ⊢St   ⊢    ⊢nat (n + m) ∷ ⊢St
  CAR   : ∀ {⊢St ty1 ty2}{⊢t1 : ⊢ ty1}{⊢t2 : ⊢ ty2}      →     ⊢pair ⊢t1 ⊢t2 ∷ ⊢St   ⊢             ⊢t1 ∷ ⊢St
  CRD   : ∀ {⊢St ty1 ty2}{⊢t1 : ⊢ ty1}{⊢t2 : ⊢ ty2}      →     ⊢pair ⊢t1 ⊢t2 ∷ ⊢St   ⊢             ⊢t2 ∷ ⊢St
  PAIR  : ∀ {⊢St ty1 ty2}{⊢t1 : ⊢ ty1}{⊢t2 : ⊢ ty2}      →         ⊢t1 ∷ ⊢t2 ∷ ⊢St   ⊢   ⊢pair ⊢t1 ⊢t2 ∷ ⊢St
  PUSH  : ∀ {⊢St}  →  (ty : Type)(x : ℕ)                 →                     ⊢St   ⊢          ⊢nat x ∷ ⊢St     -- extend PUSH for any base types (need to define base types first)
  NIL   : ∀ {⊢St}  →  (ty : Type)                        →                     ⊢St   ⊢   ⊢[] {ty = ty} ∷ ⊢St

data _—→_ : ⊢Stack → ⊢Stack → Set where
  exec  : ∀ {St}                                    →   St —→ St
  _∶_   : ∀ {S1 S2 S3}  →  S1 —→ S2  →  S2 ⊢ S3     →   S1 —→ S3

Sᵢₙ  : ⊢Stack
Sᵢₙ  = ⊢pair (⊢nat 41) (⊢nat 7) ∷ []
Sₒᵤₜ : ⊢Stack
Sₒᵤₜ = ⊢pair (⊢[] {ty = ops}) (⊢nat 42) ∷ []
_ : Sᵢₙ —→ Sₒᵤₜ
_ = exec ∶ CAR ∶ PUSH nat 1 ∶ ADD ∶ NIL ops ∶ PAIR

data tyStack : Set where
  []   :                              tyStack
  _∷_  : ∀ (ty : Type)  → tyStack  →  tyStack

⊢2ty : ⊢Stack → tyStack
⊢2ty [] = []
⊢2ty (_∷_ {ty} x ⊢S) = ty ∷ ⊢2ty ⊢S

s : ⊢Stack
s = ⊢pair (⊢nat 3) (⊢pair ⊢unit (⊢nat 42)) ∷ ⊢unit ∷ []
_ : (⊢2ty s) ≡ (pair nat (pair unit nat) ∷ unit ∷ [])
_ = refl

data _↦_ : tyStack → tyStack → Set where
  ADD   : ∀ {tyS}                                        →         nat ∷ nat ∷ tyS   ↦             nat ∷ tyS
  CAR   : ∀ {tyS ty1 ty2}                                →      pair ty1 ty2 ∷ tyS   ↦             ty1 ∷ tyS
  CRD   : ∀ {tyS ty1 ty2}                                →      pair ty1 ty2 ∷ tyS   ↦             ty2 ∷ tyS
  PAIR  : ∀ {tyS ty1 ty2}                                →         ty1 ∷ ty2 ∷ tyS   ↦    pair ty1 ty2 ∷ tyS
  PUSH  : ∀ {tyS}  →  (ty : Type)(x : ℕ)                 →                     tyS   ↦             nat ∷ tyS     -- extend PUSH for any base types (need to define base types first)
  NIL   : ∀ {tyS}  →  (ty : Type)                        →                     tyS   ↦         list ty ∷ tyS

{-
data Contract[p:_s:_prg:_] : Type → Type → 
  >> this is where it get's a bit to ridiculous, i dont wan't a program to be something i can't proveably connect to a typed stack ... and i don't want to call it typed stack actually ;{ ...
  next steps:
    * more general classification of a program
      > program should only be a list of commands
      > typechecking should be possible against contract definition,
        which only gives the type of parameters and storage, not typed values like above
        so i'll need to:
        + define a "stack type" that is the current stack without values
    * for this purpose it would also be helpful (and even more so later on) to define
      a datatype for the instructions
-}
