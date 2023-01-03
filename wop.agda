
module Michelson-separate-minimal where

infix  3  Contract[p:_s:_prg:_]
infix  3  typechecked:_
infix  4  _⊢_↠_
infix  4  _f⊢_⇒_
infix  4  _s⊢_⇒_
infixr 7  _f∣_
infixr 7  _s∣_
infixr 7  _;∣_

open import Michelson-Base public

------ TYPING ----------------------------------------------------------------------------

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
  DROP     : ∀ {ST n}                  → (top : Stack Type) → length top ≡ n                                   →  DROP     n           s⊢       top ++ ST  ⇒                  ST
  DIG      : ∀ {ST ty n}               → (top : Stack Type) → length top ≡ n                                   →  DIG      n           s⊢  top ++ ty ∷ ST  ⇒      ty ∷ top ++ ST
  DUG      : ∀ {ST ty n}               → (top : Stack Type) → length top ≡ n                                   →  DUG      n           s⊢  ty ∷ top ++ ST  ⇒      top ++ ty ∷ ST
  DUP      : ∀ {ST ty n}               → (top : Stack Type) → length top + 1 ≡ n                               →  DUP      n           s⊢  top ++ ty ∷ ST  ⇒ ty ∷ top ++ ty ∷ ST

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

------ SEMANTICS ------------------------------------------------------------------------

impl : ∀ {inst args result} →   inst f⊢ args ⇒ result  →  ⟦ args ⇒ result ⟧
impl  ADD          = _+_
impl  CAR          = proj₁
impl  CDR          = proj₂
impl  PAIR         = _,_
impl (PUSH ty x)   = x
impl (NIL  ty)     = []
impl  CONS         = _∷_
impl  UNIT         = tt
impl  SOME         = just
impl (NONE ty)     = nothing
impl  COMPARE n m  with n <? m
...   | yes _ = - 0
...   | no  _ with n ≟ m
...   | yes _ = + 0
...   | no  _ = + 1
impl  LT           = λ{ (+_ n) → false ; (-_ n) → true }

------ ... applied to full Stack --------------------------------------------------------

data MatchTypes : Stack Type → fullStack → Set where
  []   : ∀ {     fS}                                                   →  MatchTypes         []              fS
  _∷_  : ∀ {args fS}  →  ((ty , x) : Σ Type ⟦_⟧) → MatchTypes args fS  →  MatchTypes (ty ∷ args) ((ty , x) ∷ fS)
  -- could also be written with implicit extension like this : ∀ {args fS ty}{x : ⟦ ty ⟧} → MatchTypes args fS → MatchTypes (ty ∷ args) ((ty , x) ∷ fS)

apply : ∀ {result fS args} → ⟦ args ⇒ result ⟧ → MatchTypes args fS → ⟦ result ⟧
apply f                [] = f
apply f ((_ , x) ∷ match) = apply (f x) match

unchanged : ∀ {args fS} → MatchTypes args fS → fullStack
unchanged ([] {rS}) = rS
unchanged (_ ∷ mch) = unchanged mch

--==== W I P ============================================================================

-----------------------------------------------------------------------------------------

{-
infix  4  _//_,_↦_,_

data _//_,_↦_,_ : Prog → fullStack → fullStack → fullStack → fullStack → Set where
  terminate : ∀ {rS sS}                                                                            →                end //                    fS   , sS  ↦ fS    , sS
  _f↦_      : ∀ {inst args result rSin prg rSout sS}
              → (typing : inst f⊢ args ⇒ result)
              → (match : MatchTypes args rSin)
              → prg // (result , apply (impl typing) match) ∷ unchanged match , sS ↦ rSout , sS    →         inst ; prg //                    fSin , sS  ↦ fSout , sS
  blubb     : ∀ {iter type 
              →                                                                                    →    ITER iter ; prg // (list type , []) ∷ fSin , sS  ↦ fSout , sS
  
infix  4  _/_↦_
infix  4  _//_↦_

data _/_↦_ : Inst → fullStack → fullStack → Set where
  functional : ∀ {inst args result fS} {typing : inst f⊢ args ⇒ result} {match : MatchTypes args fS}
               →    inst    /    fS  ↦  (result , apply (impl typing) match) ∷ unchanged match

data _//_↦_ : Prog → fullStack → fullStack → Set where
  terminate : ∀ {fS}                                                                     →           end // fS   ↦ fS
  _f↦_      : ∀ {inst args result fSin prg fSout}
              → (typing : inst f⊢ args ⇒ result)
              → (match : MatchTypes args fSin)
              → prg // (result , apply (impl typing) match) ∷ unchanged match ↦ fSout    →    inst ; prg // fSin ↦ fSout
  --_s‌↦_      : 
  
  i want to execute:
    ITER  prg //  (list ty , [...]) :: fS  ↦ fS'
  for that i need to know how
  NOOOOOOOOOOOOO ... start over:
  assume i know that:
    prg // (ty , x) ∷ fS ↦ fS'
  then i can conclude that:
    ITER prg / (list ty , x ∷ tl) ∷ fS ↦ ... done, i need the full double stack!!!


---- old stuff: ---------------------------------------------------------------------
  structural : ∀ {inst rSi rSo} → inst // rSi , [] ↦ rSo , []
               →    inst    /    rSi ↦ rSo

data _//_,_↦_,_ : Inst → fullStack → fullStack → fullStack → fullStack → Set
infix  3  _/_,_↦_,_
data _/_,_↦_,_ : Inst → fullStack → fullStack → fullStack → fullStack → Set where
  DIPinit  : ∀ {inst top fS}                                                     → DIP inst /                top ∷ fS  ,                            []  ↦        fS  ,                top ∷ []
  DIPexec  : ∀ {inst top fSi fSo}            →  inst / fSi ↦ fSo                 → DIP inst /                      fSi ,                      top ∷ []  ↦  top ∷ fSo ,                      []
--folgende Definition von MAP ist leider falsch, hab ich aus dem Gedaechtnis erstellt ...
  MAPinit  : ∀ {inst type args fS}                                               → MAP inst / (list type , args) ∷ fS  ,                            []  ↦        fS  , (list type , args) ∷ []
  MAPstep  : ∀ {inst type top rest fSi fSo}  →  inst / (type , top) ∷ fSi ↦ fSo  → MAP inst /                      fSi , (list type , top ∷ rest) ∷ []  ↦        fSo , (list type , rest) ∷ []
  MAPexec  : ∀ {inst type top fSi fSo}       →  inst / (type , top) ∷ fSi ↦ fSo  → MAP inst /                      fSi , (list type , top ∷   []) ∷ []  ↦        fSo ,                      []

data _//_,_↦_,_ where
  sstep : ∀ {inst rSi sSi rSe sSe rSo sSo}  →  inst / rSi , sSi ↦ rSe , sSe  →  inst  / rSe , sSe ↦ rSo , sSo     →   inst // rSi , sSi ↦ rSo , sSo
  mstep : ∀ {inst rSi sSi rSe sSe rSo sSo}  →  inst / rSi , sSi ↦ rSe , sSe  →  inst // rSe , sSe ↦ rSo , sSo     →   inst // rSi , sSi ↦ rSo , sSo
-}

