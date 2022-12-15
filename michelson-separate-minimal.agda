open import Data.Nat
open import Data.Unit
open import Data.Empty
open import Data.Product
open import Data.List
open import Data.List.Membership.Propositional

module Michelson-separate-minimal where

infix  3  Contract[p:_s:_prg:_]
infix  3  typechecked:_
infix  4  _⊢_↠_
infix  4  _⊢_⇒_
infixr 6  _;_
infixl 7  _∘_

data Type : Set where
  ops nat unit            : Type
  pair : (ty1 ty2 : Type) → Type
  list : (type : Type)    → Type

data Operation : Set where
  a b c : Operation

⟦_⟧ : Type → Set
⟦ ops ⟧ = Operation
⟦ nat ⟧ = ℕ
⟦ unit ⟧ = ⊤
⟦ pair T T₁ ⟧ = ⟦ T ⟧ × ⟦ T₁ ⟧
⟦ list T ⟧ = List ⟦ T ⟧

data Inst : Set where
  ADD CAR CRD PAIR        :  Inst
  PUSH  : ∀ ty → ⟦ ty ⟧   →  Inst
  NIL   : ∀ (ty : Type)   →  Inst

data Prog : Set where
  end                     :  Prog
  _;_   : Inst → Prog     →  Prog

-- the following may not work for more complicated instructions like map!?!??
data _⊢_⇒_ : Inst → List Type → Type → Set where
  ADD   :                            ADD         ⊢      nat ∷ nat ∷ []  ⇒           nat
  CAR   : ∀ {ty1 ty2}          →     CAR         ⊢   pair ty1 ty2 ∷ []  ⇒           ty1
  CRD   : ∀ {ty1 ty2}          →     CRD         ⊢   pair ty1 ty2 ∷ []  ⇒           ty2
  PAIR  : ∀ {ty1 ty2}          →     PAIR        ⊢      ty1 ∷ ty2 ∷ []  ⇒  pair ty1 ty2
  PUSH  : ∀ ty → (x : ⟦ ty ⟧)  →     PUSH ty x   ⊢                  []  ⇒           ty
  NIL   : ∀ ty                 →     NIL  ty     ⊢                  []  ⇒      list ty

⟦_⟧↦_ : List Type → Type → Set
⟦     [] ⟧↦ T =         ⟦  T ⟧
⟦ x ∷ LT ⟧↦ T = ⟦ x ⟧ → ⟦ LT ⟧↦ T

_/ : ∀ {inst args result} →   inst ⊢ args ⇒ result  →  ⟦ args ⟧↦ result
ADD       / = _+_
CAR       / = proj₁
CRD       / = proj₂
PAIR      / = λ z z₁ → z , z₁
PUSH ty x / = x
NIL  ty   / = []

Stack = List

data _⊢_↠_ : Prog → Stack Type → Stack Type → Set where
  id    : ∀ {ST}                                         →            end   ⊢               ST   ↠ ST
  _∘_   : ∀ {resulttype argtypes STin STout prg inst}    -- order of arguments motivated by standard function concat notation f ∘ g
          → prg  ⊢ resulttype ∷ STin ↠ STout                                  
          → inst ⊢          argtypes ⇒ resulttype        →     inst ; prg   ⊢   argtypes ++ STin ↠ STout

data Contract[p:_s:_prg:_] : Type → Type → Prog → Set where
  typechecked:_ : ∀ {pt st prg}
    → prg ⊢ pair pt st ∷ [] ↠ pair (list ops) st ∷ []    →    Contract[p: pt s: st prg: prg ]

simple02con : Contract[p: nat s: nat prg: CAR ; PUSH nat 1 ; ADD ; NIL ops ; PAIR ; end ]
simple02con = typechecked: id ∘ PAIR ∘ NIL ops ∘ ADD ∘ PUSH nat 1 ∘ CAR
