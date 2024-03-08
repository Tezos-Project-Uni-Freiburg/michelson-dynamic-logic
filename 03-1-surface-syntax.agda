module 03-1-surface-syntax where

open import Data.Bool using (T)
open import Data.List using (List; []; _∷_; _++_; length; drop; take)
open import Data.List.Properties using (++-assoc)
open import Data.Nat using (_+_; _≤ᵇ_)
open import Function using (_∘_)

open import 01-Types

--! Syntax >

infixr 7  _;_

pattern [_] x = x ∷ []
pattern [_⨾_] y z    =         y ∷ z ∷ []
pattern [_⨾_⨾_] x y z    =     x ∷ y ∷ z ∷ []

--! Program {
data Program : Stack → Stack → Set
data Instruction : List Type → List Type → Set

Instruction⁺ : Stack → Stack → Set
Instruction⁺ a b = ∀ {s} → Instruction (a ++ s) (b ++ s)

data Instruction where
  ADDnn   :       Instruction⁺ [ nat ⨾ nat ]     [ nat ]
  ADDm    :       Instruction⁺ [ mutez ⨾ mutez ] [ mutez ]
  CAR     :       Instruction⁺ [ pair t₁ t₂ ]    [ t₁ ]
  CDR     :       Instruction⁺ [ pair t₁ t₂ ]    [ t₂ ]
  PAIR    :       Instruction⁺ [ t₁ ⨾ t₂ ]       [ pair t₁ t₂ ] 
  NONE    : ∀ t → Instruction⁺ []               [ option t ]
  SOME    :       Instruction⁺ [ t ]            [ option t ]
  NIL     : ∀ t → Instruction⁺ []               [ list t ]
  CONS    :       Instruction⁺ [ t ⨾ list t ]   [ list t ]
  TRANSFER-TOKENS : ∀ {pt : Passable t} → Instruction⁺ [ t ⨾  mutez ⨾ contract pt ] [ ops ]

  UNPAIR  : Instruction⁺ [ pair t₁ t₂ ] [ t₁ ⨾ t₂ ]
  SWAP    : Instruction⁺ [ t₁ ⨾ t₂ ]    [ t₂ ⨾ t₁ ]
  DUP     : Instruction⁺ [ t ]         [ t ⨾ t ]

  AMOUNT    : Instruction⁺ [] [ mutez ]
  BALANCE   : Instruction⁺ [] [ mutez ]
  CONTRACT  : (P : Passable t) → Instruction⁺  [ addr ]  [ option (contract P) ]

  DROP      :  Instruction⁺ [ t ] []
  PUSH      :  Pushable t → ⟦ t ⟧ → Instruction⁺ [] [ t ]

  DIP       : ∀ n → {T (n ≤ᵇ length S)} → Program (drop n S) Se → Instruction S (take n S ++ Se)
  ITER      : Program (t ∷ S) S → Instruction (list t ∷ S) S
  IF-NONE   : Program S Se → Program (t ∷ S) Se → Instruction (option t ∷ S) Se

data Program where
  end  : Program S S
  _;_  : Instruction  Si   So
       → Program      So   Se
       → Program      Si   Se
--! }

ex : Program [ (pair nat nat) ] [ (pair nat nat) ]
ex = DUP ; (UNPAIR ; (ADDnn ; (DROP ; end)))

ex1 : Program [ (pair nat nat) ] [ nat ]
ex1 = UNPAIR ; (SOME ; ((IF-NONE (PUSH nat 42 ; end) end) ; (DROP ; end)))


import 02-Functions-Interpretations as F

encodeP : Program Si Se → F.Program Si Se
encodeI : Instruction Si Se → F.Instruction Si Se

encodeP end = F.end
encodeP (i ; p) = (encodeI i) F.; (encodeP p)

encodeI ADDnn = F.fct (F.D1 (F.GEN2 _+_))
encodeI ADDm = F.fct (F.D1 F.ADDm)
encodeI CAR = F.fct (F.D1 F.CAR)
encodeI CDR = F.fct (F.D1 F.CDR)
encodeI PAIR = F.fct (F.D1 F.PAIR)
encodeI (NONE t) = F.fct (F.D1 (F.NONE t))
encodeI SOME = F.fct (F.D1 F.SOME)
encodeI (NIL t) = F.fct (F.D1 (F.NIL t))
encodeI CONS = F.fct (F.D1 F.CONS)
encodeI TRANSFER-TOKENS = F.fct (F.D1 F.TRANSFER-TOKENS)
encodeI UNPAIR = F.fct (F.Dm F.UNPAIR)
encodeI SWAP = F.fct (F.Dm F.SWAP)
encodeI DUP = F.fct (F.Dm F.DUP)
encodeI AMOUNT = F.enf F.AMOUNT
encodeI BALANCE = F.enf F.BALANCE
encodeI (CONTRACT P) = F.enf (F.CONTRACT P)
encodeI DROP = F.DROP
encodeI (PUSH t x) = F.fct (F.PUSH t x)
encodeI (ITER p) = F.ITER (encodeP p)
encodeI (IF-NONE pₙ pₛ) = F.IF-NONE (encodeP pₙ) (encodeP pₛ)
encodeI (DIP n {pf} p) = F.DIP n {pf} (encodeP p)

encodeSP : F.Program Si Se → F.ShadowProg Si [] Se []
encodeSP F.end = F.end
encodeSP (i F.; p) = i F.; (encodeSP p)

encode : Program Si Se → F.ShadowProg Si [] Se []
encode = encodeSP ∘ encodeP
