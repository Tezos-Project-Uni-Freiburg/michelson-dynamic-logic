module Typing where

infix  3  Contract[p:_s:_prg:_]
infix  3  typechecked:_
infix  4  _⊢_↠_
infix  4  _f⊢_⇒_
infix  4  _s⊢_⇒_
infixr 7  _f∣_
infixr 7  _s∣_
infixr 7  _;∣_

open import Base public

data _f⊢_⇒_ : Inst → List Type → Type → Set where
  ADD       :                                                  ADD         f⊢      nat ∷ nat ∷ []  ⇒           nat
  CAR       : ∀ {ty1 ty2}                                  →   CAR         f⊢   pair ty1 ty2 ∷ []  ⇒           ty1
  CDR       : ∀ {ty1 ty2}                                  →   CDR         f⊢   pair ty1 ty2 ∷ []  ⇒           ty2
  PAIR      : ∀ {ty1 ty2}                                  →   PAIR        f⊢      ty1 ∷ ty2 ∷ []  ⇒  pair ty1 ty2
  PUSH      : ∀ ty → (x : ⟦ ty ⟧)                          →   PUSH ty x   f⊢                  []  ⇒           ty
  NIL       : ∀ ty                                         →   NIL  ty     f⊢                  []  ⇒      list ty
  CONS      : ∀ {ty}                                       →   CONS        f⊢   ty ∷ list ty ∷ []  ⇒      list ty
  UNIT      :                                                  UNIT        f⊢                  []  ⇒          unit
  SOME      : ∀ {ty}                                       →   SOME        f⊢             ty ∷ []  ⇒    option ty
  NONE      : ∀ ty                                         →   NONE ty     f⊢                  []  ⇒    option ty
  COMPARE   :                                                  COMPARE     f⊢      nat ∷ nat ∷ []  ⇒           int
  LT        :                                                  LT          f⊢            int ∷ []  ⇒          bool

data _⊢_↠_ : Prog → Stack Type  → Stack Type → Set

data _s⊢_⇒_ : Inst → Stack Type → Stack Type → Set where
  IF       : ∀ {then else STi STo}     →     then ⊢                STi ↠ STo    →    else ⊢      STi ↠ STo     →  IF       then else   s⊢       bool ∷ STi ⇒                  STo
  IF-NONE  : ∀ {then else STi STo ty}  →     then ⊢                STi ↠ STo    →    else ⊢ ty ∷ STi ↠ STo     →  IF-NONE  then else   s⊢  option ty ∷ STi ⇒                  STo
  IF-CONS  : ∀ {then else STi STo ty}  →     then ⊢ ty ∷ list ty ∷ STi ↠ STo    →    else ⊢      STi ↠ STo     →  IF-CONS  then else   s⊢    list ty ∷ STi ⇒                  STo
  ITER     : ∀ {prg ty  ST}                                                     →    prg  ⊢ ty ∷ ST  ↠ ST      →  ITER           prg   s⊢    list ty ∷ ST  ⇒                  ST
  DIP      : ∀ {prg STi STo n}         → (top : Stack Type) → length top ≡ n    →    prg  ⊢      STi ↠ STo     →  DIP      n     prg   s⊢       top ++ STi ⇒           top ++ STo
  -- DIP      : ∀ {prg STi STo n}         → (top : Stack Type) → length ST  ≥ n    →    prg  ⊢      STi ↠ STo     →  DIP      n     prg   s⊢       top ++ STi ⇒           top ++ STo
  DROP     : ∀ {ST n}                  → (top : Stack Type) → length top ≡ n                                   →  DROP     n           s⊢       top ++ ST  ⇒                  ST
  DIG      : ∀ {ST ty n}               → (top : Stack Type) → length top ≡ n                                   →  DIG      n           s⊢  top ++ ty ∷ ST  ⇒      ty ∷ top ++ ST
  DUG      : ∀ {ST ty n}               → (top : Stack Type) → length top ≡ n                                   →  DUG      n           s⊢  ty ∷ top ++ ST  ⇒      top ++ ty ∷ ST
  DUP      : ∀ {ST ty n}               → (top : Stack Type) → 1 + length top ≡ n                               →  DUP      n           s⊢  top ++ ty ∷ ST  ⇒ ty ∷ top ++ ty ∷ ST
  -- maybe those rules that are only a restructuring of the stack could also be projected onto semantics similarly to 'functional' typing rules
  -- ... with an extended impl : inst ⊢ args ⇒ list result → ⟦ args ⇒ list result ⟧ ...

data _⊢_↠_ where
  id    : ∀ {ST}                                           →           end   ⊢               ST   ↠ ST
  _f∣_  : ∀ {resulttype argtypes STin STout prg inst}
          → inst f⊢           argtypes ⇒ resulttype
          → prg   ⊢  resulttype ∷ STin ↠ STout             →   inst  ; prg   ⊢   argtypes ++ STin ↠ STout
  _s∣_  : ∀ {inst STin STout prg STend}
          → inst s⊢              STin  ⇒ STout
          → prg   ⊢              STout ↠ STend             →   inst  ; prg   ⊢               STin ↠ STend
  _;∣_  : ∀ {prg1 STin STout prg2 STend}
          → prg1  ⊢              STin  ↠ STout
          → prg2  ⊢              STout ↠ STend             →   prg1 ;; prg2  ⊢               STin ↠ STend

data Contract[p:_s:_prg:_] : Type → Type → Prog → Set where
  typechecked:_ : ∀ {pt st prg}
    → prg ⊢ pair pt st ∷ [] ↠ pair (list ops) st ∷ []    →    Contract[p: pt s: st prg: prg ]
