open import Data.Nat
open import Data.Unit
open import Data.Product
open import Data.List
open import Data.List.Membership.Propositional

module ALL-Michelson-different-approaches where

infix  3  Contract[p:_s:_prg:_]
infix  3  typechecked:_
infix  4  _⊢_↠_
infix  4  _⊢_⇒_/_
infixl 7  _∘_

data Type : Set where
  ops nat unit            : Type
  pair : (ty1 ty2 : Type) → Type
  list : (type : Type)    → Type

data Operation : Set where
  a b c : Operation

⟦_⟧ : Type → Set   -- interpretation
⟦ ops ⟧ = Operation
⟦ nat ⟧ = ℕ
⟦ unit ⟧ = ⊤
⟦ pair T T₁ ⟧ = ⟦ T ⟧ × ⟦ T₁ ⟧
⟦ list T ⟧ = List ⟦ T ⟧

⟦_⇒_⟧ : List Type → Type → Set
⟦     [] ⇒ T ⟧ =              ⟦ T ⟧
⟦ A ∷ LT ⇒ T ⟧ = ⟦ A ⟧ → ⟦ LT ⇒ T ⟧

Stack = List

----------------------------------------------------------------------------------------------

module original-refined where -- very first approach with better names

  infixr 6  _;_

  data Inst : Set where
    ADD CAR CRD PAIR        :  Inst
    PUSH  : ∀ ty → ⟦ ty ⟧   →  Inst
    NIL   : ∀ (ty : Type)   →  Inst

  data Prog : Set where
    end                     :  Prog
    _;_   : Inst → Prog     →  Prog

  fullStack = Stack (Σ Type ⟦_⟧)

  infix 4 _⊢_↦_
  data _⊢_↦_ : Inst → fullStack → fullStack → Set where
    ADD   : ∀ {n m fS}          →  ADD  ⊢  (nat , n) ∷ (nat , m) ∷ fS  ↦  (nat , n + m) ∷ fS

----------------------------------------------------------------------------------------------

module no-success-here where -- this idea seems somehow too complicated to implement easily (at least as agda newby)

  infixr 6  _;_

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
  --simple-01-program  = CRD ; end -- !!! THIS WILL COMPLAIN ABOUT MISSING STUFF (YELLOW)
  --simple-01-program  = CRD ; NIL ops ; {!!} ; end

----------------------------------------------------------------------------------------------

module better-but-writing-programs-is-ugly where

  infixr 6  _;_

  data Inst : (args : List Type) → (result : Type) → ⟦ args ⇒ result ⟧ →  Set where
    ADD   :                         Inst     (nat ∷ nat ∷ [])            nat     _+_
    CAR   : ∀ {ty1 ty2}          →  Inst  (pair ty1 ty2 ∷ [])            ty1     proj₁
    CRD   : ∀ {ty1 ty2}          →  Inst  (pair ty1 ty2 ∷ [])            ty2     proj₂
    PAIR  : ∀ {ty1 ty2}          →  Inst     (ty1 ∷ ty2 ∷ [])  (pair ty1 ty2)    λ x x₁ → x , x₁
    PUSH  : ∀ ty → (x : ⟦ ty ⟧)  →  Inst                  []             ty      x
    NIL   : ∀ ty                 →  Inst                  []       (list ty)     []


  data Prog : Set where
    end   :                                                              Prog
    _;_   : ∀ {args result impl} →  Inst args result impl  →  Prog   →   Prog

  prg : Prog
  prg = (CRD {unit}{unit}) ; NIL ops ; (PAIR {unit}{unit}) ; end
  -- ich wuerde es lieber so schreiben :(
  -- prg = CRD ; NIL ops ; PAIR ; end

-- module lets-try-relational where ----------------------------------------------------------

infixr 6  _;_

data Inst : Set where
  ADD CAR CRD PAIR        :  Inst
  PUSH  : ∀ ty → ⟦ ty ⟧   →  Inst
  NIL   : ∀ (ty : Type)   →  Inst

data Prog : Set where
  end                     :  Prog
  _;_   : Inst → Prog     →  Prog

data _⊢_⇒_/_ : Inst → (args : List Type) → (result : Type) → ⟦ args ⇒ result ⟧ →  Set where
  ADD   :                         ADD        ⊢     (nat ∷ nat ∷ []) ⇒           nat   /  _+_
  CAR   : ∀ {ty1 ty2}          →  CAR        ⊢  (pair ty1 ty2 ∷ []) ⇒           ty1   /  proj₁
  CRD   : ∀ {ty1 ty2}          →  CRD        ⊢  (pair ty1 ty2 ∷ []) ⇒           ty2   /  proj₂
  PAIR  : ∀ {ty1 ty2}          →  PAIR       ⊢     (ty1 ∷ ty2 ∷ []) ⇒ (pair ty1 ty2)  /  λ x x₁ → x , x₁
  PUSH  : ∀ ty → (x : ⟦ ty ⟧)  →  PUSH ty x  ⊢                  []  ⇒           ty    /  x
  NIL   : ∀ ty                 →  NIL  ty    ⊢                  []  ⇒     (list ty)   /  []

data _⊢_↠_ : Prog → Stack Type → Stack Type → Set where
  id    : ∀ {ST}                                    →          end   ⊢           ST   ↠ ST
  _∘_   : ∀ {args result STin STout prg inst a→r}
          →  prg  ⊢ result ∷ STin ↠ STout                                  
          →  inst ⊢          args ⇒ result / a→r    →   inst ; prg   ⊢   args ++ STin ↠ STout

data Contract[p:_s:_prg:_] : Type → Type → Prog → Set where
  typechecked:_ : ∀ {pt st prg}
    → prg ⊢ pair pt st ∷ [] ↠ pair (list ops) st ∷ []    →    Contract[p: pt s: st prg: prg ]

simple02con : Contract[p: nat s: nat prg: CAR ; PUSH nat 1 ; ADD ; NIL ops ; PAIR ; end ]
simple02con = typechecked: (id ∘ PAIR ∘ NIL ops ∘ ADD ∘ PUSH nat 1) ∘ CAR
--simple02con = typechecked: id ∘ PAIR ∘ NIL ops ∘ ADD ∘ PUSH nat 1 ∘ CAR -- only almost automatic typechecking
{-
-}
