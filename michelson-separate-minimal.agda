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
-- some infix _/impl 

------ BASICS --------------------------------------------------------------------------------

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

------ TYPING --------------------------------------------------------------------------------

-- the following may not work for more complicated instructions like map!?!??
-- it will also not work for some very easy instructions like DUP!!!!!
data _⊢_⇒_ : Inst → List Type → Type → Set where
  ADD   :                            ADD         ⊢      nat ∷ nat ∷ []  ⇒           nat
  CAR   : ∀ {ty1 ty2}          →     CAR         ⊢   pair ty1 ty2 ∷ []  ⇒           ty1
  CRD   : ∀ {ty1 ty2}          →     CRD         ⊢   pair ty1 ty2 ∷ []  ⇒           ty2
  PAIR  : ∀ {ty1 ty2}          →     PAIR        ⊢      ty1 ∷ ty2 ∷ []  ⇒  pair ty1 ty2
  PUSH  : ∀ ty → (x : ⟦ ty ⟧)  →     PUSH ty x   ⊢                  []  ⇒           ty
  NIL   : ∀ ty                 →     NIL  ty     ⊢                  []  ⇒      list ty

Stack = List

data _⊢_↠_ : Prog → Stack Type → Stack Type → Set where
  id    : ∀ {ST}                                         →            end   ⊢               ST   ↠ ST
  _∘_   : ∀ {resulttype argtypes STin STout prg inst}
          → prg  ⊢ resulttype ∷ STin ↠ STout                                  
          → inst ⊢          argtypes ⇒ resulttype        →     inst ; prg   ⊢   argtypes ++ STin ↠ STout

data Contract[p:_s:_prg:_] : Type → Type → Prog → Set where
  typechecked:_ : ∀ {pt st prg}
    → prg ⊢ pair pt st ∷ [] ↠ pair (list ops) st ∷ []    →    Contract[p: pt s: st prg: prg ]

simple02con : Contract[p: nat s: nat prg: CAR ; PUSH nat 1 ; ADD ; NIL ops ; PAIR ; end ]
simple02con = typechecked: id ∘ PAIR ∘ NIL ops ∘ ADD ∘ PUSH nat 1 ∘ CAR

------ SEMANTICS -----------------------------------------------------------------------------

⟦_⇒_⟧ : List Type → Type → Set
⟦     [] ⇒ T ⟧ =              ⟦ T ⟧
⟦ A ∷ LT ⇒ T ⟧ = ⟦ A ⟧ → ⟦ LT ⇒ T ⟧

_/impl : ∀ {inst args result} →   inst ⊢ args ⇒ result  →  ⟦ args ⇒ result ⟧
ADD       /impl = _+_
CAR       /impl = proj₁
CRD       /impl = proj₂
PAIR      /impl = λ z z₁ → z , z₁
PUSH ty x /impl = x
NIL  ty   /impl = []

--==== W I P ===============================================================================--

fullStack = Stack (Σ Type ⟦_⟧)

--_$$_ : ∀ {

module exec-as-data-set where

  infix  4  _/_↦_
  data _/_↦_ : Inst → fullStack → fullStack → Set where
    step0 : ∀ {inst result}{remainingStack : fullStack}
              (i⊢[]⇒r   : inst ⊢                                     [] ⇒  result)
            →             inst /                         remainingStack ↦ (result ,  i⊢[]⇒r /impl)          ∷ remainingStack
    step1 : ∀ {inst a0 v0 result}{remainingStack : fullStack}
              (i⊢a0⇒r   : inst ⊢  a0                   ∷             [] ⇒  result)
            →             inst / (a0 , v0)             ∷ remainingStack ↦ (result , (i⊢a0⇒r /impl) v0)      ∷ remainingStack
    step2 : ∀ {inst a0 a1 v0 v1 result}{remainingStack : fullStack}
              (i⊢args⇒r : inst ⊢  a0       ∷  a1       ∷             [] ⇒  result)
            →             inst / (a0 , v0) ∷ (a1 , v1) ∷ remainingStack ↦ (result , (i⊢args⇒r /impl) v0 v1) ∷ remainingStack


{-
  _/_↦_ : Inst → (fullStack → fullStack → Set)
  _/_↦_ ADD = ∀ {n m fS}    →    ADD / (nat , n) ∷ (nat , m) ∷ fS ↦ (nat , (ADD /impl) n m) ∷ fS
  -- bzw irgendwie noch eleganter (man darf ja wohl noch traeumen ;)
  ∀ {...} inst / argsTV ∷ fS ↦ (result , (i⊢a⇒r /impl) argsV) ∷ fS
-}

--- different approach: Stack of values instead of fullStack:

{- backup
fS2⊢ : fullStack → Stack Type
fS2⊢ [] = []
fS2⊢ ((ty , _) ∷ fS) = ty ∷ fS2⊢ fS

-}
