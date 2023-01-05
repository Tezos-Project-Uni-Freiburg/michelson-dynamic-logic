
module partial-everything where

open import Base public
open import Level using (Level)

private
  variable
    a : Level
    A : Set a
    
_∷ₘ_ : A → Maybe (List A) → Maybe (List A)
a ∷ₘ mla with mla
... | nothing = nothing
... | just as = just (a ∷ as)

_≟ₗₜ_ : DecidableEquality (List Type)
[] ≟ₗₜ [] = yes refl
[] ≟ₗₜ (x ∷ ms) = no (λ ())
(x ∷ ls) ≟ₗₜ [] = no (λ ())
(x ∷ ls) ≟ₗₜ (y ∷ ms) with x ≟ₜ y
... | no  x≢y  = no λ{ refl → x≢y refl } 
... | yes refl with ls ≟ₗₜ ms
... | no  l≢m  = no λ{ refl → l≢m refl } 
... | yes refl = yes refl

------ TYPING ---------------------------------------------------------------------------

infix  4  _f⊢_⇒_
data _f⊢_⇒_ : Inst → List Type → Type → Set where
  ADD       :                                                  ADD         f⊢      nat ∷ nat ∷ []  ⇒           nat
  CAR       : ∀ {ty1 ty2}                                  →   CAR         f⊢   pair ty1 ty2 ∷ []  ⇒           ty1
  CDR       : ∀ {ty1 ty2}                                  →   CDR         f⊢   pair ty1 ty2 ∷ []  ⇒           ty2
  PAIR      : ∀ {ty1 ty2}                                  →   PAIR        f⊢      ty1 ∷ ty2 ∷ []  ⇒  pair ty1 ty2
  PUSH      : ∀ ty → (x : ⟦ ty ⟧)                          →   PUSH ty x   f⊢                  []  ⇒           ty
  NIL       : ∀ ty                                         →   NIL  ty     f⊢                  []  ⇒      list ty

-- impl : ∀ {inst args result} →   inst f⊢ args ⇒ result  →  ⟦ args ⇒ result ⟧
functional-typing₁ : Inst → Maybe (List Type × Type)
functional-typing₁ ADD = just (nat ∷ nat ∷ [] , nat)
functional-typing₁ _ = nothing
-- this way i cannot express ... basically any other Inst

functional-typing₂ : Inst → List Type → Maybe Type
functional-typing₂ ADD (nat ∷ nat ∷ []) = just nat
functional-typing₂ CAR (pair t1 t2 ∷ []) = just t1
functional-typing₂ _ _ = nothing
-- this way i cant do the following that i was aiming for:
typepartition : Stack Type → Stack Type → Maybe ((Stack Type) × (Stack Type))
typepartition ST [] = just ([] , ST)
typepartition [] (t ∷ args) = nothing
typepartition (t ∷ ST) (at ∷ args) with t ≟ₜ at
... | no  _ = nothing
... | yes _ with typepartition ST args
...   | nothing = nothing
...   | just (Targs , Trest) = just (t ∷ Targs , Trest)
inst-typing₁ : Inst → Stack Type → Maybe (Stack Type)
inst-typing₁ inst ST with functional-typing₁ inst
... | nothing = nothing
... | just (args , result) with typepartition ST args
...   | nothing = nothing
...   | just (argsT , restT) = just (result ∷ restT)

functional : Inst → Maybe ℕ
functional CAR = just 1
functional CDR = just 1
functional ADD = just 2
functional _ = nothing

split : Maybe ℕ → List A → Maybe (List A × List A)
split nothing              _  = nothing
split (just  zero)        xs  = just ([] , xs)
split (just (suc n))      []  = nothing
split (just (suc n)) (x ∷ xs) with split (just n) xs
... | nothing = nothing
... | just (top , bottom) = just (x ∷ top , bottom)

inst-typing₃ : Inst → Stack Type → Maybe (Stack Type)
inst-typing₃ inst ST with split (functional inst) ST
... | nothing = nothing
... | just (args , rest) = {!!}
-- inst-typing₃ 
-- inst-typing₃ _ _ = nothing

mutual

  inst-typing : Inst → Stack Type → Maybe (Stack Type)
  inst-typing CAR (pair t1 t2 ∷ ST) = just (t1 ∷ ST)
  inst-typing CDR (pair t1 t2 ∷ ST) = just (t2 ∷ ST)
  inst-typing (DIP zero prg) ST = prog-typing prg ST
  inst-typing (DIP (suc n) prg) (t ∷ ts) = t ∷ₘ (inst-typing (DIP n prg) ts)
  inst-typing (PUSH t x) ST = just (t ∷ ST)
  inst-typing (ITER prg) (list t ∷ ST) with prog-typing prg (t ∷ ST)
  ... | nothing = nothing
  ... | just STout with STout ≟ₗₜ ST
  ... | no  _    = nothing
  ... | yes refl = just ST
  inst-typing ADD (nat ∷ nat ∷ ST) = just (nat ∷ ST)
  inst-typing (NIL t) ST = just (list t ∷ ST)
  inst-typing PAIR (t1 ∷ t2 ∷ ST) = just (pair t1 t2 ∷ ST)
  inst-typing _ _ = nothing

  prog-typing : Prog → Stack Type → Maybe (Stack Type)
  prog-typing end ST = just ST
  prog-typing (inst ; prg) STin with inst-typing inst STin
  ... | nothing = nothing
  ... | just STout = prog-typing prg STout

addElems-program = CAR ; DIP 1 (PUSH nat 0 ; end) ; ITER (ADD ; end) ; NIL ops ; PAIR ; end
addElems-STin = pair (list nat) nat ∷ []
addElems-STend = prog-typing addElems-program addElems-STin
open import Data.Maybe
_ : from-just (prog-typing addElems-program addElems-STin) ≡ pair (list ops) nat ∷ []
_ = refl

------ SEMANTICS ------------------------------------------------------------------------

stacktype : fullStack → Stack Type
stacktype [] = []
stacktype ((t , x) ∷ fs) = t ∷ (stacktype fs)

inst-semantics : Inst → fullStack → Maybe fullStack
inst-semantics ADD ((nat , n) ∷ (nat , m) ∷ fS) = just ((nat , n + m) ∷ fS)
inst-semantics CAR ((pair t1 t2 , x , y) ∷ fS) = just ((t1 , x) ∷ fS)
inst-semantics _ _ = nothing

prog-step : Inst → Prog → fullStack → fullStack → Maybe (Prog × fullStack × fullStack)
prog-step (ITER  iterprog) prog ((list ty , xs) ∷ fS) sS = just (ITER' iterprog ; prog , fS , (list ty , xs) ∷ sS)
prog-step (ITER' iterprog) prog fS ((list ty , x ∷ xs) ∷ sS) = just (iterprog ;; ITER' iterprog ; prog , (ty , x) ∷ fS , (list ty , xs) ∷ sS)
prog-step (ITER' iterprog) prog fS ((list ty , []) ∷ sS) = just (prog , fS , sS)
prog-step inst prog rS sS with inst-semantics inst rS
... | nothing = nothing
... | just fSout = just (prog , fSout , sS)

-- impl : Inst → Maybe (⟦_⟧)
-- impl (PUSH ty x)   = ?
{-
impl  ADD          = _+_
impl : ∀ {inst args result} →   inst f⊢ args ⇒ result  →  ⟦ args ⇒ result ⟧
impl  CAR          = proj₁
impl  CDR          = proj₂
impl  PAIR         = _,_
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

------ lets try partial functions ... ---------------------------------------------------

partition : fullStack → Stack Type → Maybe (fullStack × fullStack)
partition fS [] = just ([] , fS)
partition [] (aty ∷ args) = nothing
partition (tx@(ty , x) ∷ fS) (aty ∷ args) with ty ≟ₜ aty
... | no  _ = nothing
... | yes _ with partition fS args
... | nothing = nothing
... | just (argsStack , remainingStack) = just (tx ∷ argsStack , remainingStack)
-}

-- addElems-inStack : fullStack
-- addElems-inStack = (pair (list nat) nat , 1 ∷ 2 ∷ 3 ∷ [] , 42) ∷ []

-- Sin-part = partition addElems-inStack (pair (list nat) nat ∷ [])
--step : fullStack → Inst


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

