open import Data.Nat
open import Data.Unit
open import Data.Product using (_×_; Σ; _,_)
open import Data.List
open import Data.List.Membership.Propositional

blubb = 4

module Michelson-separate where
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

  Stack = List

  data _⊢_⇒_ : Inst → Stack Type → Stack Type → Set where
    ADD   : ∀ {tS}           →  ADD        ⊢     nat ∷ nat ∷ tS   ⇒             nat ∷ tS
    CAR   : ∀ {tS ty1 ty2}   →  CAR        ⊢  pair ty1 ty2 ∷ tS   ⇒             ty1 ∷ tS
    CRD   : ∀ {tS ty1 ty2}   →  CRD        ⊢  pair ty1 ty2 ∷ tS   ⇒             ty2 ∷ tS
    PAIR  : ∀ {tS ty1 ty2}   →  PAIR       ⊢     ty1 ∷ ty2 ∷ tS   ⇒    pair ty1 ty2 ∷ tS
    PUSH  : ∀ {tS} (n)       →  PUSH nat n ⊢                 tS   ⇒             nat ∷ tS
    NIL   : ∀ {tS} (ty)      →  NIL ty     ⊢                 tS   ⇒         list ty ∷ tS

  data _⊢_↠_ : Prog → Stack Type → Stack Type → Set where
    id    : ∀ {tS}                         →         end  ⊢  tS  ↠ tS
    _∘_   : ∀ {tS1 tS2 tS3 prg inst}
            → prg  ⊢ tS2 ↠ tS3
            → inst ⊢ tS1 ⇒ tS2             →  inst ; prg  ⊢  tS1 ↠ tS3

  data Contract[p:_s:_prg:_] : Type → Type → Prog → Set where
    typechecked:_ : ∀ {pt st prg}
      → prg ⊢ pair pt st ∷ [] ↠ pair (list ops) st ∷ []    →    Contract[p: pt s: st prg: prg ]

  simple02con : Contract[p: nat s: nat prg: CAR ; PUSH nat 1 ; ADD ; NIL ops ; PAIR ; end ]
  simple02con = typechecked: (((((id ∘ PAIR) ∘ NIL ops) ∘ ADD) ∘ PUSH 1) ∘ CAR)
  --simple02con = typechecked: id ∘ PAIR ∘ NIL ops ∘ ADD ∘ PUSH 1 ∘ CAR
