open import Data.Nat
open import Data.Unit
open import Data.Product using (_×_; Σ; _,_)
open import Data.List
open import Data.List.Membership.Propositional

module Michelson-singledef-minimal where

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


module too-complicated-for-now where
  --[⟦_⟧] : this should give me a set with arbitrary currying so to speek :D
  --data Inst :  ...  something like this: → (map ⟦_⟧ args → ⟦ result ⟧) →  Set where
  data Inst : (args : List Type) → (result : Type) → ({!!} → ⟦ result ⟧) →  Set where
    ADD   :               Inst  (nat ∷ nat ∷ [])  nat  {!!} -- would like to put _+_ here ...

⊢Args = List (Σ Type ⟦_⟧)
data Inst : ⊢Args → (Σ Type ⟦_⟧) → Set where
  ADD   : ∀ {n m}                →   Inst    ((nat , n) ∷ (nat , m) ∷ [])            (nat , n + m)
  CAR   : ∀ {ty1 ty2 x y}        →   Inst   ((pair ty1 ty2 , x , y) ∷ [])            (ty1 , x    )
  CRD   : ∀ {ty1 ty2 x y}        →   Inst   ((pair ty1 ty2 , x , y) ∷ [])            (ty2 ,     y)
  PAIR  : ∀ {ty1 ty2 x y}        →   Inst    ((ty1 , x) ∷ (ty2 , y) ∷ [])   (pair ty1 ty2 , x , y)
  PUSH  : ∀ ty → (x : ⟦ ty ⟧)    →   Inst                             []             (ty  , x    )
  NIL   : ∀ ty                   →   Inst                             []        (list ty  ,    [])

data Prog : Set where
  end                                             :  Prog
  _;_   : ∀ {args res} → Inst args res → Prog     →  Prog   -- ... so hab ich mir das nicht vorgestellt :(

crd : Inst ((pair unit unit , tt , tt) ∷ []) (unit , tt)
crd = CRD
simple-01-program  = CRD ; end
--simple-01-program  = CRD ; NIL ops ; {!!} ; end

{-
  +-----------+
  |   FAZIT   |
  +-----------+

    Es macht die Sache bislang NICHT einfacher

    > evtl kann man da noch was raus holen, wenn ich mich mit Agda noch etwas besser auskenne und noch mehr intrinsisch type ... evtl mal in der Zukunft ;P
  


data _⊢_⇒_ : Inst → List Type → Type → Set where
  ADD   :                        ADD         ⊢      nat ∷ nat ∷ []  ⇒           nat
  CAR   : ∀ {ty1 ty2}      →     CAR         ⊢   pair ty1 ty2 ∷ []  ⇒           ty1
  CRD   : ∀ {ty1 ty2}      →     CRD         ⊢   pair ty1 ty2 ∷ []  ⇒           ty2
  PAIR  : ∀ {ty1 ty2}      →     PAIR        ⊢      ty1 ∷ ty2 ∷ []  ⇒  pair ty1 ty2
  PUSH  : ∀ {ty x}         →     PUSH ty x   ⊢                  []  ⇒           ty
  NIL   : ∀ {ty}           →     NIL  ty     ⊢                  []  ⇒      list ty

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
simple02con = typechecked: id ∘ PAIR ∘ NIL ∘ ADD ∘ PUSH ∘ CAR
-}
