module 03-3-bigstep-execution where

open import Data.Bool using (true; false; T)
open import Data.Maybe using (nothing; just)
open import Data.Nat using (_+_; _≤ᵇ_)
open import Data.List using ([]; _∷_; length; drop)
open import Data.List.Relation.Unary.All using (All; _∷_; []; head; tail)
open import Data.Product

open import Relation.Binary.PropositionalEquality hiding ([_])

import 00-All-Utilities as H
open import 01-Types
open import 02-Functions-Interpretations
open import 03-2-concrete-execution

-- big step semantics as defined in the Michelson documentation

record Configuration (ri : Stack) : Set where
  constructor Conf
  field
    cenv : CEnvironment
    stk  : All ⟦_⟧ ri

data [_,_]⇓_ : ∀ {ri ro} → Configuration ri → Program ri ro → All ⟦_⟧ ro → Set

data [_,_]⤋_ : ∀ {ri ro} → Configuration ri → ShadowProg{⟦_⟧} ri ro → All ⟦_⟧ ro → Set

data [_,_]↓′_ : ∀ {ri ro} → Configuration ri → ShadowInst ri ro → All ⟦_⟧ ro → Set where
  ↓-MPUSH1 : ∀ {t ts ce}  {x : ⟦ t ⟧} {xs : All ⟦_⟧ ts}
    → [ Conf ce xs , MPUSH1 x ]↓′ (x ∷ xs)

data [_,_]↓_ : ∀ {ri ro} → Configuration ri → Instruction ri ro → All ⟦_⟧ ro → Set where
  ↓-PUSH : ∀ {t ts ce} {P : Pushable t} {x : ⟦ t ⟧} {xs : All ⟦_⟧ ts}
    → [ Conf ce xs , PUSH P x ]↓ (x ∷ xs)
  ↓-GEN1 : ∀ {t t′ ts ce} {f : ⟦ t ⟧ → ⟦ t′ ⟧} {x : ⟦ t ⟧} {xs : All ⟦_⟧ ts}
    → [ Conf ce (x ∷ xs) , GEN1 f ]↓ (f x ∷ xs)
  ↓-GEN2 : ∀ {t₁ t₂ t′ ts ce} {f : ⟦ t₁ ⟧ → ⟦ t₂ ⟧ → ⟦ t′ ⟧} {x₁ : ⟦ t₁ ⟧} {x₂ : ⟦ t₂ ⟧} {xs : All ⟦_⟧ ts}
    → [ Conf ce (x₁ ∷ x₂ ∷ xs) , GEN2 f ]↓ (f x₁ x₂ ∷ xs)
  ↓-ADDnn : ∀ {ts ce} {x₁ : ⟦ nat ⟧} {x₂ : ⟦ nat ⟧} {xs : All ⟦_⟧ ts}
    → [ Conf ce (x₁ ∷ x₂ ∷ xs) , ADDnn ]↓ (x₁ + x₂ ∷ xs)
  ↓-ADDm : ∀ {ts ce} {x₁ : ⟦ mutez ⟧} {x₂ : ⟦ mutez ⟧} {xs : All ⟦_⟧ ts}
    → [ Conf ce (x₁ ∷ x₂ ∷ xs) , ADDm ]↓ (x₁ + x₂ ∷ xs)
  ↓-SUB-MUTEZ : ∀ {ts ce} {x₁ : ⟦ mutez ⟧} {x₂ : ⟦ mutez ⟧} {xs : All ⟦_⟧ ts}
    → [ Conf ce (x₁ ∷ x₂ ∷ xs) , SUB-MUTEZ ]↓ (sub-mutez x₁ x₂ ∷ xs)
  ↓-CAR : ∀ {t₁ t₂ ts ce} {x₁ : ⟦ t₁ ⟧} {x₂ : ⟦ t₂ ⟧} {xs : All ⟦_⟧ ts}
    → [ Conf ce ((x₁ , x₂) ∷ xs) , CAR ]↓ (x₁ ∷ xs)
  ↓-CDR : ∀ {t₁ t₂ ts ce} {x₁ : ⟦ t₁ ⟧} {x₂ : ⟦ t₂ ⟧} {xs : All ⟦_⟧ ts}
    → [ Conf ce ((x₁ , x₂) ∷ xs) , CDR ]↓ (x₂ ∷ xs)
  ↓-NIL : ∀ {t ts ce} {xs : All ⟦_⟧ ts}
    → [ Conf ce xs , NIL t ]↓ ([] ∷ xs)
  ↓-NONE : ∀ {t ts ce} {xs : All ⟦_⟧ ts}
    → [ Conf ce xs , NONE t ]↓ (nothing ∷ xs)
  ↓-SOME : ∀ {t ts ce} {x₁ : ⟦ t ⟧} {xs : All ⟦_⟧ ts}
    → [ Conf ce (x₁ ∷ xs) , SOME ]↓ (just x₁ ∷ xs)
  ↓-CONS : ∀ {t ts ce} {x₁ : ⟦ t ⟧} {x₂ : ⟦ list t ⟧} {xs : All ⟦_⟧ ts}
    → [ Conf ce (x₁ ∷ x₂ ∷ xs) , CONS ]↓ ((x₁ ∷ x₂) ∷ xs)
  ↓-PAIR : ∀ {t₁ t₂ ts ce} {x₁ : ⟦ t₁ ⟧} {x₂ : ⟦ t₂ ⟧} {xs : All ⟦_⟧ ts}
    → [ Conf ce (x₁ ∷ x₂ ∷ xs) , PAIR ]↓ ((x₁ , x₂) ∷ xs)
  ↓-UNPAIR : ∀ {t₁ t₂ ts ce} {x₁ : ⟦ t₁ ⟧} {x₂ : ⟦ t₂ ⟧} {xs : All ⟦_⟧ ts}
    → [ Conf ce ((x₁ , x₂) ∷ xs) , UNPAIR ]↓ (x₁ ∷ x₂ ∷ xs)
  ↓-SWAP : ∀ {t₁ t₂ ts ce} {x₁ : ⟦ t₁ ⟧} {x₂ : ⟦ t₂ ⟧} {xs : All ⟦_⟧ ts}
    → [ Conf ce (x₁ ∷ x₂ ∷ xs) , SWAP ]↓ (x₂ ∷ x₁ ∷ xs)
  ↓-DUP : ∀ {t₁ ts ce} {x₁ : ⟦ t₁ ⟧} {xs : All ⟦_⟧ ts}
    → [ Conf ce (x₁ ∷ xs) , DUP ]↓ (x₁ ∷ x₁ ∷ xs)
  ↓-AMOUNT : ∀ {ts ce} {xs : All ⟦_⟧ ts}
    → [ Conf ce xs , AMOUNT ]↓ (Environment.amount ce ∷ xs)
  ↓-BALANCE : ∀ {ts ce} {xs : All ⟦_⟧ ts}
    → [ Conf ce xs , BALANCE ]↓ (Environment.balance ce ∷ xs)
  ↓-CONTRACT : ∀ {t ts ce} {P : Passable t} {x₁ : ⟦ addr ⟧} {xs : All ⟦_⟧ ts}
    → [ Conf ce (x₁ ∷ xs) , CONTRACT P ]↓ (appcontract P ce x₁ ∷ xs)
  ↓-TRANSFER-TOKENS : ∀ {t ts ce} {P : Passable t} {x₁ : ⟦ t ⟧} {x₂ : ⟦ mutez ⟧} {x₃ : ⟦ contract P ⟧} {xs : All ⟦_⟧ ts}
    → [ Conf ce (x₁ ∷ x₂ ∷ x₃ ∷ xs) , fct (D1 (`TRANSFER-TOKENS {t}{P})) ]↓ (transfer-tokens {t} {P} x₁ x₂ x₃ ∷ xs)
  ↓-DROP : ∀ {t ts ce} {x : ⟦ t ⟧} {xs : All ⟦_⟧ ts}
    → [ Conf ce (x ∷ xs) , DROP ]↓ xs
  ↓-DIP : ∀ {ts ce} {xs : All ⟦_⟧ ts} {ys} {n} {q : T (n ≤ᵇ length ts)} {prg : Program (drop n ts) ro}
    → [ Conf ce (H.drop n xs) , prg ]⇓ ys
    → [ Conf ce xs , DIP n {q} prg ]↓ (H.take n xs H.++ ys)
  ↓-ITER-[] :  ∀ {t ts ce} {x : ⟦ list t ⟧} {xs : All ⟦_⟧ ts} {prg : Program (t ∷ ts) ts} → [ Conf ce ([] ∷ xs) , ITER prg ]↓ xs
  ↓-ITER-∷  :  ∀ {t ts ce} {x₁ : ⟦ t ⟧}{x₂ : ⟦ list t ⟧} {xs ys zs : All ⟦_⟧ ts} {prg : Program (t ∷ ts) ts}
    → [ Conf ce (x₁ ∷ xs) , prg ]⇓ ys
    → [ Conf ce (x₂ ∷ ys) , ITER prg ]↓ zs
    → [ Conf ce ((x₁ ∷ x₂) ∷ xs) , ITER prg ]↓ zs
  ↓-IF-NONE : ∀ {t ts ce} {xs : All ⟦_⟧ ts} {ys : All ⟦_⟧ ro} {prg-none : Program ts ro} {prg-some : Program (t ∷ ts) ro}
    → [ Conf ce xs , prg-none ]⇓ ys
    → [ Conf ce (nothing ∷ xs) , IF-NONE prg-none prg-some ]↓ ys
  ↓-IF-SOME : ∀ {t ts ce} {x : ⟦ t ⟧} {xs : All ⟦_⟧ ts} {ys : All ⟦_⟧ ro} {prg-none : Program ts ro} {prg-some : Program (t ∷ ts) ro}
    → [ Conf ce (x ∷ xs) , prg-some ]⇓ ys
    → [ Conf ce (just x ∷ xs) , IF-NONE prg-none prg-some ]↓ ys
  
data [_,_]⇓_ where

  ⇓-end : ∀ {ts ce} {xs : All ⟦_⟧ ts}
    → [ Conf ce xs , end ]⇓ xs
  ⇓-seq : ∀ {ts ts₁ ts₂ ce} {xs : All ⟦_⟧ ts} {ys : All ⟦_⟧ ts₁} {zs : All ⟦_⟧ ts₂} {ins : Instruction ts ts₁} {prg : Program ts₁ ts₂}
    → [ Conf ce xs , ins ]↓ ys
    → [ Conf ce ys , prg ]⇓ zs
    → [ Conf ce xs , ins ; prg ]⇓ zs


data [_,_]⤋_ where

  ⤋-end : ∀ {ts ce} {xs : All ⟦_⟧ ts}
    → [ Conf ce xs , end ]⤋ xs
  ⤋-seq : ∀ {ts ts₁ ts₂ ce} {xs : All ⟦_⟧ ts} {ys : All ⟦_⟧ ts₁} {zs : All ⟦_⟧ ts₂} {ins : Instruction ts ts₁} {prg : ShadowProg ts₁ ts₂}
    → [ Conf ce xs , ins ]↓ ys
    → [ Conf ce ys , prg ]⤋ zs
    → [ Conf ce xs , ins ; prg ]⤋ zs
  ⤋-shadow : ∀ {ts ts₁ ts₂ ce} {xs : All ⟦_⟧ ts} {ys : All ⟦_⟧ ts₁} {zs : All ⟦_⟧ ts₂} {ins : ShadowInst ts ts₁} {prg : ShadowProg ts₁ ts₂}
    → [ Conf ce xs , ins ]↓′ ys
    → [ Conf ce ys , prg ]⤋ zs
    → [ Conf ce xs , ins ∙ prg ]⤋ zs

-- prove soundness: if we make a prog-step, then the result remains the same.

concat-⤋ : ∀ {ce ts ts₁ ts₂} {xs : All ⟦_⟧ ts}{xs₁ : All ⟦_⟧ ts₁}{xs₂ : All ⟦_⟧ ts₂} {prg₁}
  → ∀ prg
  → [ Conf ce xs , prg ]⇓ xs₁
  → [ Conf ce xs₁ , prg₁ ]⤋ xs₂
  → [ Conf ce xs , prg ;∙ prg₁ ]⤋ xs₂
concat-⤋ end ⇓-end prg₁⤋xs₂ = prg₁⤋xs₂
concat-⤋ (ins ; prg) (⇓-seq ↓-ins prg⤋xs₁) prg₁⤋xs₂ = ⤋-seq ↓-ins (concat-⤋ prg prg⤋xs₁ prg₁⤋xs₂)

mpush1-⤋ :  ∀ {ce t ts′} (x : ⟦_⟧ t) {xs′ : All ⟦_⟧ ts′} {ys : All ⟦_⟧ ro} {prg}
  → [ Conf ce (x ∷ xs′) , prg ]⤋ ys
  → [ Conf ce xs′ , MPUSH1 x ∙ prg ]⤋ ys
mpush1-⤋ x prg⤋ys = ⤋-shadow ↓-MPUSH1 prg⤋ys

mpush-⤋ : ∀ {ce ts ts′} (xs : All ⟦_⟧ ts) {xs′ : All ⟦_⟧ ts′} {ys : All ⟦_⟧ ro} {prg}
  → [ Conf ce (xs H.++ xs′) , prg ]⤋ ys
  → [ Conf ce xs′ , mpush xs prg ]⤋ ys
mpush-⤋ [I] prg⤋ys = prg⤋ys
mpush-⤋ (x ∷ xs) prg⤋ys = mpush-⤋ xs (mpush1-⤋ x prg⤋ys)

smallstep-soundness-⤋ : ∀ {ce ts ts′} {xs : All ⟦_⟧ ts} {xs′ : All ⟦_⟧ ts′} {ys : All ⟦_⟧ ro} (prg : ShadowProg ts ro) {prg′ : ShadowProg ts′ ro}
  → [ Conf ce xs , prg ]⤋ ys
  → prog-step (cstate ce prg xs) ≡ cstate ce prg′ xs′
  → [ Conf ce xs′ , prg′ ]⤋ ys
smallstep-soundness-⤋ end prg⤋ys refl = prg⤋ys
smallstep-soundness-⤋ (MPUSH1 x ∙ prg) (⤋-shadow ↓-MPUSH1 prg⤋ys) refl = prg⤋ys
smallstep-soundness-⤋ (AMOUNT ; prg) (⤋-seq ↓-AMOUNT prg⤋ys) refl = prg⤋ys
smallstep-soundness-⤋ (BALANCE ; prg) (⤋-seq ↓-BALANCE prg⤋ys) refl = prg⤋ys
smallstep-soundness-⤋ (CONTRACT P ; prg) (⤋-seq ↓-CONTRACT prg⤋ys) refl = prg⤋ys
smallstep-soundness-⤋ (GEN1 x ; prg) (⤋-seq ↓-GEN1 prg⤋ys) refl = prg⤋ys
smallstep-soundness-⤋ (GEN2 x ; prg) (⤋-seq ↓-GEN2 prg⤋ys) refl = prg⤋ys
smallstep-soundness-⤋ (ADDnn ; prg) (⤋-seq ↓-ADDnn prg⤋ys) refl = prg⤋ys
smallstep-soundness-⤋ (ADDm ; prg) (⤋-seq ↓-ADDm prg⤋ys) refl = prg⤋ys
smallstep-soundness-⤋ (CAR ; prg) (⤋-seq ↓-CAR prg⤋ys) refl = prg⤋ys
smallstep-soundness-⤋ (CDR ; prg) (⤋-seq ↓-CDR prg⤋ys) refl = prg⤋ys
smallstep-soundness-⤋ (PAIR ; prg) (⤋-seq ↓-PAIR prg⤋ys) refl = prg⤋ys
smallstep-soundness-⤋ (NIL t ; prg) (⤋-seq ↓-NIL prg⤋ys) refl = prg⤋ys
smallstep-soundness-⤋ (NONE t ; prg) (⤋-seq ↓-NONE prg⤋ys) refl = prg⤋ys
smallstep-soundness-⤋ (SOME ; prg) (⤋-seq ↓-SOME prg⤋ys) refl = prg⤋ys
smallstep-soundness-⤋ (CONS ; prg) (⤋-seq ↓-CONS prg⤋ys) refl = prg⤋ys
smallstep-soundness-⤋ (SUB-MUTEZ ; prg) (⤋-seq ↓-SUB-MUTEZ prg⤋ys) refl = prg⤋ys
smallstep-soundness-⤋ (TRANSFER-TOKENS ; prg) (⤋-seq ↓-TRANSFER-TOKENS prg⤋ys) refl = prg⤋ys
smallstep-soundness-⤋ (UNPAIR ; prg) (⤋-seq ↓-UNPAIR prg⤋ys) refl = prg⤋ys
smallstep-soundness-⤋ (SWAP ; prg) (⤋-seq ↓-SWAP prg⤋ys) refl = prg⤋ys
smallstep-soundness-⤋ (DUP ; prg) (⤋-seq ↓-DUP prg⤋ys) refl = prg⤋ys
smallstep-soundness-⤋ (PUSH P x ; prg) (⤋-seq ↓-PUSH prg⤋ys) refl = prg⤋ys
smallstep-soundness-⤋ (DROP ; prg) (⤋-seq ↓-DROP prg⤋ys) refl = prg⤋ys
smallstep-soundness-⤋ (ITER prg-iter ; prg) (⤋-seq ↓-ITER-[] prg⤋ys) refl = prg⤋ys
smallstep-soundness-⤋ (ITER prg-iter ; prg) (⤋-seq (↓-ITER-∷ prg-iter⤋x₁ iter-prg-iter⤋x₂) prg⤋ys) refl = concat-⤋ prg-iter prg-iter⤋x₁ (⤋-shadow ↓-MPUSH1 (⤋-seq iter-prg-iter⤋x₂ prg⤋ys))
smallstep-soundness-⤋ (DIP n prg-dip ; prg) (⤋-seq (↓-DIP prg-dip⤋ys₁) prg⤋ys) refl = concat-⤋ prg-dip prg-dip⤋ys₁ (mpush-⤋ _ prg⤋ys)
smallstep-soundness-⤋ (IF-NONE prg-none prg-some ; prg) (⤋-seq (↓-IF-NONE prg-none⤋ys₁) prg⤋ys) refl = concat-⤋ prg-none prg-none⤋ys₁ prg⤋ys
smallstep-soundness-⤋ (IF-NONE prg-none prg-some ; prg) (⤋-seq (↓-IF-SOME prg-some⤋ys₁) prg⤋ys) refl = concat-⤋ prg-some prg-some⤋ys₁ prg⤋ys
