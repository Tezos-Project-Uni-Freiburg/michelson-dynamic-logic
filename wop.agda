
module wop where

open import Base public
open import Typing public

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

------ lets try partial functions ... ---------------------------------------------------

partition : fullStack → Stack Type → Maybe (fullStack × fullStack)
partition fS [] = just ([] , fS)
partition [] (aty ∷ args) = nothing
partition (tx@(ty , x) ∷ fS) (aty ∷ args) with ty ≟ₜ aty
... | no  _ = nothing
... | yes _ with partition fS args
... | nothing = nothing
... | just (argsStack , remainingStack) = just (tx ∷ argsStack , remainingStack)

addElems-program = CAR ; DIP 1 (PUSH nat 0 ; end) ; ITER (ADD ; end) ; NIL ops ; PAIR ; end
addElems-inStack : fullStack
addElems-inStack = (pair (list nat) nat , 1 ∷ 2 ∷ 3 ∷ [] , 42) ∷ []

Sin-part = partition addElems-inStack (pair (list nat) nat ∷ [])



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

