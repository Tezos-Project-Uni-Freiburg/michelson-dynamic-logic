open import Data.Nat
open import Data.Unit
open import Data.Product
open import Data.List
open import Data.List.Membership.Propositional

-- infix  2  _→ₛ_
-- infix  3  _[_,_,_,_]
infix  6  _⊢_
infix  6  _⊢Fml
infixr 6  _;_

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

Stack = List (Σ Type ⟦_⟧)
MState = Stack

Context = List Type

-- haette das gerne so geschrieben wie Sie:
-- data _⊢_ (Γ : Context) : Type → Set where
-- ... brauch ich evtl 'mutual' hier?
data _⊢_   : Context → Type → Set       -- Def 2.3, but including FSym from Def 2.2, don't know how to do that serarately in Agda?!
data _⊢Fml : Context → Set

data _⊢_ where                   
  `_               : ∀ {Γ A}          →  A ∈ Γ                       →   Γ ⊢              A
  `unit            : ∀ {Γ}                                           →   Γ ⊢           unit
  `nat             : ∀ {Γ}            →  (n : ℕ)                     →   Γ ⊢            nat    -- not sure about this one, guess it will be different when i properly introduce base types
  _`+_             : ∀ {Γ}            →  Γ ⊢ nat → Γ ⊢ nat           →   Γ ⊢            nat
  `pair            : ∀ {Γ ty1 ty2}    →  Γ ⊢ ty1 → Γ ⊢ ty2           →   Γ ⊢   pair ty1 ty2
  `_⟨⟩             : ∀ {Γ}            →  (ty : Type)                 →   Γ ⊢        list ty    -- also not very good to inline this way ...
  `_∷_             : ∀ {Γ ty}         →  Γ ⊢ ty  → Γ ⊢ list ty       →   Γ ⊢        list ty
  if_then_else_    : ∀ {Γ ty}         →  Γ ⊢Fml  → Γ ⊢ ty → Γ ⊢ ty   →   Γ ⊢             ty

data _⊢Stack : Context → Set where
  []   : ∀ {Γ}                            →  Γ ⊢Stack
  _∷_  : ∀ {Γ ty}  →  Γ ⊢ ty  → Γ ⊢Stack  →  Γ ⊢Stack

box : Context → Set
box Γ = Prog × (Γ ⊢Stack) × (Γ ⊢Stack)

data _⊢Fml where
  true false       : ∀ {Γ}                                           →   Γ ⊢Fml
  _≐_              : ∀ {Γ ty1 ty2}    →  Γ ⊢ ty1  → Γ ⊢ ty2          →   Γ ⊢Fml
  _≐ₛ_             : ∀ {Γ}            →  Γ ⊢Stack → Γ ⊢Stack         →   Γ ⊢Fml
  ¬_               : ∀ {Γ}            →  Γ ⊢Fml                      →   Γ ⊢Fml
  _∧_ _∨_ _⇀_ _↔_  : ∀ {Γ}            →  Γ ⊢Fml   → Γ ⊢Fml           →   Γ ⊢Fml 
  `∀_ `∃_          : ∀ {Γ A}          →  (A ∷ Γ) ⊢Fml                →   Γ ⊢Fml

{-
data state : (Γ : Context) → Prog → Γ ⊢Stack → Γ ⊢Stack → Γ ⊢Fml → Set where
  init     : ∀ {Γ pty sty prg}
           → Contract[p: pty s: sty prg: prg ]
           → (param : Γ ⊢ pty) → (storage : Γ ⊢ sty)
           → state Γ prg ((`pair param storage) ∷ []) [] true
  _[_,_,_,_] : ∀ (Γ : Context)
           → (prg : Prog)(S1 S2 : Γ ⊢Stack)(Φ : Γ ⊢Fml)
           → state Γ prg S1 S2 Φ
  final    : ∀ {Γ pty sty prg}
           → Contract[p: pty s: sty prg: prg ]
           → (opslist : Γ ⊢ list ops) → (storage : Γ ⊢ sty)
           → (Φ : Γ ⊢Fml)
           → state Γ end ((`pair opslist storage) ∷ []) [] Φ

simple01prg : Prog
simple01prg = CRD ; NIL ops ; PAIR ; end
simple01con : Contract[p: unit s: unit prg: simple01prg ]
simple01con = typechecked: id ∘ PAIR ∘ NIL ops ∘ CRD

state0 : state ∅ _ _ _ _
state0 = init simple01con `unit `unit

state1 : state _ _ _ _ _
state1 = ∅ [ NIL ops ; PAIR ; end , `unit ∷ [] , [] , true ]

state2 : state _ _ _ _ _
state2 = ∅ [ PAIR ; end , ` ops ⟨⟩ ∷ `unit ∷ [] , [] , true ]

state3 : state ∅ _ _ _ _
state3 = final simple01con ` ops ⟨⟩ `unit true

data _→ₛ_ : ∀ {Γ Δ inst prg s11 s12 s21 s22 Φ Ψ} → state Γ (inst ; prg) s11 s12 Φ → state Δ prg s21 s22 Ψ → Set where
  CRD↦  :  ∀ {Γ prg ty1 ty2 s1 s2 Φ}{a : Γ ⊢ ty1}{b : Γ ⊢ ty2}   →   Γ [ CRD ; prg , (`pair a b) ∷ s1 , s2 , Φ ]  →ₛ  Γ [ prg , b ∷ s1 , s2 , Φ ]

--------------------------------------------------------------------------------------

  _CRDₑₓ   : ∀ {prg ty1 ty2}{a : Γ ⊢ ty1}{b : Γ ⊢ ty2}{S1 S2 : Γ ⊢Stack}{Φ : Γ ⊢Fml}
           → [ CRD ; prg , (`pair a b) ∷ S1 , S2 , Φ ]
           →    [    prg ,           b ∷ S1 , S2 , Φ ]

data [_,_,_,_] {Γ : Context} : Prog → Γ ⊢Stack → Γ ⊢Stack → Γ ⊢Fml → Set where
  init     : ∀ {pty sty prg}
           → Contract[p: pty s: sty prg: prg ]
           → (param : Γ ⊢ pty) → (storage : Γ ⊢ sty)
           →    [ prg , (`pair param storage) ∷ [] , [] , true ]
  any      : (prg : Prog)(S1 S2 : Γ ⊢Stack)(Φ : Γ ⊢Fml)   →  [ prg , S1 , S2 , Φ ]
  final    : ∀ {pty sty prg}
           → Contract[p: pty s: sty prg: prg ]
           → (opslist : Γ ⊢ list ops) → (storage : Γ ⊢ sty)
           → (Φ : Γ ⊢Fml)
           →    [ end , (`pair opslist storage) ∷ [] , [] , Φ ]

state0 : [ simple01prg , _ , [] {Γ = ∅} , _ ]
state0 = init simple01con `unit `unit

state1 : [ NIL ops ; PAIR ; end , _ , [] {Γ = ∅} , _ ]
state1 = any (NIL ops ; PAIR ; end) (`unit ∷ []) [] true

state2 : [ PAIR ; end , _ , [] {Γ = ∅} , _ ]
state2 = any (PAIR ; end) (` ops ⟨⟩ ∷ `unit ∷ []) [] true

state3 : [ end , _ , [] {Γ = ∅} , _ ]
state3 = final simple01con ` ops ⟨⟩ `unit true

  _ADDₑₓ   : ∀ {prg}{n m : Γ ⊢ nat}{S1 S2 : Γ ⊢Stack}{Φ : Γ ⊢Fml}
           → [ ADD ; prg ,   n ∷ m  ∷ S1 , S2 , Φ ]
           →    [    prg , (n `+ m) ∷ S1 , S2 , Φ ] 
  _CARₑₓ   : ∀ {prg ty1 ty2}{a : Γ ⊢ ty1}{b : Γ ⊢ ty2}{S1 S2 : Γ ⊢Stack}{Φ : Γ ⊢Fml}
           → [ CAR ; prg , (`pair a b) ∷ S1 , S2 , Φ ]
           →    [    prg ,           a ∷ S1 , S2 , Φ ]
  _PAIRₑₓ  : ∀ {prg ty1 ty2}{a : Γ ⊢ ty1}{b : Γ ⊢ ty2}{S1 S2 : Γ ⊢Stack}{Φ : Γ ⊢Fml}
           → [ PAIR ; prg ,       a ∷ b ∷ S1 , S2 , Φ ]
           →    [     prg , (`pair a b) ∷ S1 , S2 , Φ ]
  _PUSHₑₓ  : ∀ {prg n}{S1 S2 : Γ ⊢Stack}{Φ : Γ ⊢Fml}
           → [ PUSH n ; prg ,            S1 , S2 , Φ ]
           →    [       prg , (`nat n) ∷ S1 , S2 , Φ ]
  _NILₑₓ   : ∀ {prg ty}{S1 S2 : Γ ⊢Stack}{Φ : Γ ⊢Fml}
           → [ NIL ty ; prg ,            S1 , S2 , Φ ]
           →    [       prg , (`nat n) ∷ S1 , S2 , Φ ]

  next steps:
      > i wanna be able to prove, for example for my simple02 program, that:
        * making a transfer to it with a parameter x : nat (and enough gas etc)
        * it will terminate with a new storage x+1
      > guess i'll quickly implement the framework given in the paper and then see about
        my proof goals more precisely ...
        ... easier said then done :{ ...
        what do we know about the calculus??
        * it operates on SEQUENTs Φ ⇨ Ψ
          Φ ≔ { φ₁ , … , φₙ }
          Ψ ≔ { ψ₁ , … , ψₘ }
          Φ ⇨ Ψ iff φ₁ ∧ … ∧ φₙ ⇀ ψ₁ ∨ … ∨ ψₘ
          ... this is already quite a handful :(
        * there are a bunch of sequent rules of the form
            Γ₁ ⇨ Δ₁  Γ₂ ⇨ Δ₂
            ----------------
                 Γ ⇨ Δ
          soundness proof of the calculus uses soundness of each of these rules
          rules are given as "classes" of which INSTANCES (for real formulas) can be derived
        * chapter 3 "only" introduces such rules for program modalities ⟨prg⟩
        * so my goal for this example would be do be able do derive the sequent:
          par≐41 ⇀ ⟨simple02⟩(stor≐42)
        ! that would be the goal using FOL/DL techniqes from the Key textbook, but
          using what he has given me in the document sounds somehow so much simpler!!!!!!
        Problems:
        * 
-}
