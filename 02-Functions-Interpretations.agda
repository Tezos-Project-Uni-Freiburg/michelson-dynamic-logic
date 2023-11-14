
module 02-Functions-Interpretations where

open import 01-Types

open import Relation.Binary.PropositionalEquality hiding ([_])

open import Function.Base

open import Data.Bool.Base
open import Data.Nat hiding (_/_)
open import Data.List.Base hiding ([_])
open import Data.Maybe.Base
open import Data.Product
open import Data.Unit.Base


pattern         [_]       z    =             z ∷ []
pattern       [_/_]     y z    =         y ∷ z ∷ []
pattern     [_/_/_]   x y z    =     x ∷ y ∷ z ∷ []
pattern      [_//_]       z xs =             z ∷ xs
pattern    [_/_//_]     y z xs =         y ∷ z ∷ xs
pattern  [_/_/_//_]   x y z xs =     x ∷ y ∷ z ∷ xs

data 1-func : Stack → Type → Set where
  ADDnn   :                      1-func          [ base   nat / base   nat ]  (  base nat)
  ADDm    :                      1-func          [ base mutez / base mutez ]  (base mutez)
  CAR     : ∀ {t1 t2}          → 1-func                       [ pair t1 t2 ]           t1
  CDR     : ∀ {t1 t2}          → 1-func                       [ pair t1 t2 ]           t2
  PAIR    : ∀ {t1 t2}          → 1-func                          [ t1 / t2 ]  (pair t1 t2)
  NIL     : ∀  ty              → 1-func                                   []  (   list ty)
  NONE    : ∀  ty              → 1-func                                   []  ( option ty)
  SOME    : ∀ {ty}             → 1-func                               [ ty ]  ( option ty)
  CONS    : ∀ {ty}             → 1-func                     [ ty / list ty ]  (   list ty)
  TRANSFER-TOKENS : ∀ {ty pt}  → 1-func [ ty / base mutez / contract {ty} pt ]         ops

data m-func : Stack → Stack × Type → Set where
  UNPAIR  : ∀ {t1 t2}       → m-func             [ pair t1 t2 ]   ([ t1 ] , t2)
  SWAP    : ∀ {t1 t2}       → m-func                [ t1 / t2 ]   ([ t2 ] , t1)
  DUP     : ∀ {ty}          → m-func                     [ ty ]   ([ ty ] , ty)

data env-func : Stack → Type → Set where
  AMOUNT          :            env-func             []                (base mutez)
  BALANCE         :            env-func             []                (base mutez)
  CONTRACT        : ∀ {ty} P → env-func  [ base addr ]  (option (contract {ty} P))

data Operation : Set

⟦_⟧ : Type → Set
⟦ base unit  ⟧ = ⊤
⟦ base nat   ⟧ = ℕ
⟦ base addr  ⟧ = ℕ
⟦ base mutez ⟧ = ℕ
⟦ ops        ⟧ = Operation
⟦ pair T T₁  ⟧ = ⟦ T ⟧ × ⟦ T₁ ⟧
⟦ list T     ⟧ = List  ⟦ T ⟧
⟦ option T   ⟧ = Maybe ⟦ T ⟧
⟦ contract P ⟧ = ⟦ base addr ⟧

data func-type : Stack → Stack × Type → Set where
  D1    : ∀ {result args}  → 1-func args result   →  func-type args    ([] , result)
  Dm    : ∀ {args results} → m-func args results  →  func-type args          results
  PUSH  : ∀ {ty}           → Pushable ty → ⟦ ty ⟧ →  func-type []      ([] ,     ty)

data Operation where
  transfer-tokens : ∀ {ty} {P : Passable ty}
                  → ⟦ ty ⟧ → ⟦ base mutez ⟧ → ⟦ contract P ⟧ → Operation

⟦_⇒_⟧ : Stack → Stack × Type → Set
⟦            [] ⇒          [] , r ⟧ =                     ⟦ r ⟧
⟦            [] ⇒ [ x // rl ] , r ⟧ = ⟦ x ⟧ × ⟦   [] ⇒ rl , r ⟧
⟦ [ a // args ] ⇒          result ⟧ = ⟦ a ⟧ → ⟦ args ⇒ result ⟧

infixr 5 _∷_
data Int : Stack → Set where
  [I]  : Int []
  _∷_ : ∀ {ty Γ} → ⟦ ty ⟧ → Int Γ → Int (ty ∷ Γ)

Itop : ∀ {top S} → Int (top ++ S) → Int top
Itop {[]} γ = [I]
Itop {[ ty // top ]} (x ∷ γ) = x ∷ Itop {top} γ

Ibot : ∀ {top S} → Int (top ++ S) → Int S
Ibot {[]} γ = γ
Ibot {[ ty // top ]} (x ∷ γ) = Ibot {top} γ

takeI : ∀ {S} n → Int S → Int (take n S)
takeI zero I = [I]
takeI (suc n) [I] = [I]
takeI (suc n) (x ∷ I) = x ∷ (takeI n I)

dropI : ∀ {S} n → Int S → Int (drop n S)
dropI zero I = I
dropI (suc n) [I] = [I]
dropI (suc n) (x ∷ I) = dropI n I

infixr 10 _+I+_
_+I+_ : ∀ {top S} → Int top → Int S → Int (top ++ S)
[I] +I+ γ = γ
(x ∷ γtop) +I+ γ = x ∷ γtop +I+ γ

impl : ∀ {args result} → func-type args result → ⟦ args ⇒ result ⟧
impl (D1 ADDnn)     = _+_
impl (D1 ADDm)      = _+_
impl (D1 CAR)       = proj₁
impl (D1 CDR)       = proj₂
impl (D1 PAIR)      = _,_
impl (D1 (NIL ty))  = []
impl (D1 (NONE ty)) = nothing
impl (D1 SOME)      = just
impl (D1 CONS)      = _∷_
impl (Dm UNPAIR)    = id
impl (Dm SWAP)      = λ z z₁ → z₁ , z
impl (Dm DUP)       = λ z → z , z
impl (PUSH P x)     = x
impl (D1 (TRANSFER-TOKENS {ty} {pt})) = λ x tok cont
                                        → transfer-tokens {ty} {pt} x tok cont

[×_] : Stack × Type → Stack
[×           [] , ty ] = [ ty                 ]
[× [ tz // lt ] , ty ] = [ tz // [× lt , ty ] ]

apply : ∀ {args result} → ⟦ args ⇒ result ⟧ → Int args → Int [× result ]
apply {result =           [] , ty}       f  [I] = f  ∷ [I]
apply {result = [ tz // lt ] , ty} (f₁ , f) [I] = f₁ ∷ apply f [I]
apply f (x ∷ Iargs) = apply (f x) Iargs

getvalue : ∀ {ty} → Int [ ty ] → ⟦ ty ⟧
getvalue (x ∷ [I]) = x

appD1 : ∀ {args result} → 1-func args result → Int args → ⟦ result ⟧
appD1 1f Iargs = getvalue (apply (impl (D1 1f)) Iargs)

appft : ∀ {args result} → func-type args result → Int args → Int [× result ]
appft (D1 1f) Iargs = (appD1 1f Iargs) ∷ [I]
appft ft Iargs = apply (impl ft) Iargs

------------------------- Instructions and Programs -------------------------------------

infixr 7  _;_
infixr 7  _∙_
infixr 6  _;;_
-- infixr 6  _∙∙_
infixr 6  _;∙_

data Instruction : Stack → Stack → Set

data Program : Stack → Stack → Set where
  end  : ∀ {S} → Program S S
  _;_  : ∀ {Si So Se}
       → Instruction  Si   So
       → Program      So   Se
       → Program      Si   Se

open import Relation.Nullary.Decidable using (True; toWitness)

data Instruction where
  enf       : ∀ {args result S}
            → env-func args result
            → Instruction  (       args ++ S )       [ result // S ]
  fct       : ∀ {args results S}
            → func-type args results
            → Instruction  (       args ++ S )  ([× results ] ++ S)
  DROP      : ∀ {ty S}
            → Instruction  [         ty // S ]                   S
  ITER      : ∀ {ty S}
            → Program      [         ty // S ]                   S
            → Instruction  [    list ty // S ]                   S
  -- DIP       : ∀ top {S Se} 
  DIP       : ∀ {S Se} n → {T (n ≤ᵇ length S)}
            -- → (n : ℕ) → {top : Stack} → {True (n ≟ₙ length top)}
            -- → (n : ℕ) → {top : Stack} → {n ≡ length top}
            -- → Program                      S                     Se
            -- → Instruction  (        top ++ S )           (top ++ Se)
            → Program              (drop n S)                    Se
            → Instruction  (               S )           (take n S ++ Se)
  IF-NONE   : ∀ {ty S Se}
            → Program                      S                     Se
            → Program      [         ty // S ]                   Se
            → Instruction  [  option ty // S ]                   Se

_;;_ : ∀ {Si So Se} → Program Si So → Program So Se → Program Si Se
end     ;; g = g
(i ; p) ;; g = i ; (p ;; g)

data ShadowInst : Stack → Stack → Stack → Stack → Set where
  ITER'     : ∀ {ty rS sS}
            → Program      [ ty // rS ]                              rS
            → ShadowInst           rS   [ list ty // sS ]            rS  sS
  DIP'      : ∀ top {rS sS}
  -- DIP'      : ∀ {rS sS} n → {T (n ≤ᵇ length sS)}
            -- → (n : ℕ) → {True (n ≟ₙ length top)}
            → ShadowInst           rS        (top ++ sS )    (top ++ rS) sS
          -- → ShadowInst           rS                sS    (take n sS ++ rS) (drop n sS)

data ShadowProg : Stack → Stack → Stack → Stack → Set where
  end  : ∀ {rS sS} → ShadowProg rS sS rS sS
  _;_  : ∀ {ri rn si ro so}
       → Instruction ri     rn
       → ShadowProg  rn si  ro so
       → ShadowProg  ri si  ro so
  _∙_  : ∀ {ri si rn sn ro so}
       → ShadowInst  ri si  rn sn
       → ShadowProg  rn sn  ro so
       → ShadowProg  ri si  ro so
  
_;∙_   : ∀ {ri rn si ro so}
       → Program ri rn → ShadowProg rn si ro so → ShadowProg ri si ro so
end     ;∙ g = g
(i ; p) ;∙ g = i ; (p ;∙ g)

