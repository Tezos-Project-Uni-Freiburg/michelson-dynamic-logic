module 03-3-bigstep-execution where

open import Data.Unit
open import Data.Bool using (Bool; true; false; T)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Nat using (ℕ; zero; suc; _+_; _≤ᵇ_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (suc-injective; +-suc)
open import Data.List using (List; []; _∷_; length; drop; take; _++_)
open import Data.List.Relation.Unary.All using (All; _∷_; []; head; tail)
open import Data.Product

open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; sym; cong; cong-app; subst)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)

import 00-All-Utilities as H
open import 01-Types
open import 02-Functions-Interpretations
open import 03-2-concrete-execution

-- trivial nat lemma

suc-k : ∀ k → suc k ≡ k + 1
suc-k zero = refl
suc-k (suc k) = cong suc (suc-k k)

-- list lemma

length-take : ∀ {A : Set} k (xs : List A) → k ≤ length xs  → length (take k xs) ≡ k
length-take zero [] z≤n = refl
length-take zero (_ ∷ xs) z≤n = refl
length-take (suc k) [] ()
length-take (suc k) (_ ∷ xs) (s≤s k≤len-xs) = cong suc (length-take k xs k≤len-xs)

-- reflection

≤ᵇ-suc : ∀ k m → T (suc k ≤ᵇ suc m) → T (k ≤ᵇ m)
≤ᵇ-suc zero m w = tt
≤ᵇ-suc (suc k) (suc m) w = w

≤ᵇ⇒≤ : ∀ {A : Set} k (ts : List A) → T (k ≤ᵇ length ts) → k ≤ length ts
≤ᵇ⇒≤ zero ts w = z≤n
≤ᵇ⇒≤ (suc k) (_ ∷ ts) w = s≤s (≤ᵇ⇒≤ k ts (≤ᵇ-suc k (length ts) w))

-- lemma about prog-step

prog-step*-+ : ∀ {cs : CProgState ro} n₁ n₂
  → prog-step* (n₁ + n₂) cs ≡ prog-step* n₂ (prog-step* n₁ cs)
prog-step*-+ zero n₂ = refl
prog-step*-+ (suc n₁) n₂ = prog-step*-+ n₁ n₂


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

----------------------------------------
prog-step*-mpush : ∀ {ce} {ts}{ts′} k (xs : All ⟦_⟧ ts) {xs′ : All ⟦_⟧ ts′} {prg : ShadowProg (ts ++ ts′) ro} (p : length ts ≡ k) 
  → prog-step* k (cstate ce (mpush xs prg) xs′) ≡ cstate ce prg (xs H.++ xs′)
prog-step*-mpush zero [] p = refl
prog-step*-mpush {ce = ce} (suc k) (x ∷ xs) {xs′} {prg} p =
  let ih = prog-step*-mpush k xs (suc-injective p) in
  begin
    prog-step* (suc k) (cstate ce (mpush ([ x ]++ xs) prg) xs′)
  ≡⟨ cong (λ □ → prog-step* □ (cstate ce (mpush ([ x ]++ xs) prg) xs′)) (suc-k k) ⟩
    prog-step* (k + 1) (cstate ce (mpush ([ x ]++ xs) prg) xs′)
  ≡⟨ prog-step*-+ k 1 ⟩
    prog-step* 1 (prog-step* k (cstate ce (mpush ([ x ]++ xs) prg) xs′))
  ≡⟨ cong (prog-step* 1) ih ⟩
    prog-step* 1 (cstate ce (MPUSH1 x ∙ prg) (xs H.++ xs′))
  ≡⟨ refl ⟩
    cstate ce prg ((x ∷ xs) H.++ _)
  ∎
  
------------------------------------------

bigins⇒smallstep : ∀ {ce ts ts₁} {xs : All ⟦_⟧ ts} {ys : All ⟦_⟧ ts₁}
  → {prg : ShadowProg ts₁ ro}
  → (ins : Instruction ts ts₁)
  → [ Conf ce xs , ins ]↓ ys
  → ∃[ n ] prog-step* n (cstate ce (ins ; prg) xs) ≡ cstate ce prg ys

bigstep⇒smallstep : ∀ {ce ts} {xs : All ⟦_⟧ ts} {ys : All ⟦_⟧ ro} (prg : ShadowProg ts ro)
  → [ Conf ce xs , prg ]⤋ ys
  → ∃[ n ] prog-step* n (cstate ce prg xs) ≡ cstate ce end ys

bigstep1⇒smallstep : ∀ {ce ts ts′} {xs : All ⟦_⟧ ts} {xs′ : All ⟦_⟧ ts′} {prg′  : ShadowProg ts′ ro} (prg : Program ts ts′)
  → [ Conf ce xs , prg ]⇓ xs′
  → ∃[ n ] prog-step* n (cstate ce (prg ;∙ prg′) xs) ≡ cstate ce prg′ xs′

bigins⇒smallstep .(PUSH _ _) ↓-PUSH = suc zero , refl
bigins⇒smallstep .(GEN1 _) ↓-GEN1 = suc zero , refl
bigins⇒smallstep .(GEN2 _) ↓-GEN2 = suc zero , refl
bigins⇒smallstep .ADDnn ↓-ADDnn = suc zero , refl
bigins⇒smallstep .ADDm ↓-ADDm = suc zero , refl
bigins⇒smallstep .SUB-MUTEZ ↓-SUB-MUTEZ = suc zero , refl
bigins⇒smallstep .CAR ↓-CAR = suc zero , refl
bigins⇒smallstep .CDR ↓-CDR = suc zero , refl
bigins⇒smallstep .(NIL _) ↓-NIL = suc zero , refl
bigins⇒smallstep .(NONE _) ↓-NONE = suc zero , refl
bigins⇒smallstep .SOME ↓-SOME = suc zero , refl
bigins⇒smallstep .CONS ↓-CONS = suc zero , refl
bigins⇒smallstep .PAIR ↓-PAIR = suc zero , refl
bigins⇒smallstep .UNPAIR ↓-UNPAIR = suc zero , refl
bigins⇒smallstep .SWAP ↓-SWAP = suc zero , refl
bigins⇒smallstep .DUP ↓-DUP = suc zero , refl
bigins⇒smallstep .AMOUNT ↓-AMOUNT = suc zero , refl
bigins⇒smallstep .BALANCE ↓-BALANCE = suc zero , refl
bigins⇒smallstep .(CONTRACT _) ↓-CONTRACT = suc zero , refl
bigins⇒smallstep .TRANSFER-TOKENS ↓-TRANSFER-TOKENS = suc zero , refl
bigins⇒smallstep .DROP ↓-DROP = suc zero , refl
bigins⇒smallstep {ro = ro}{ce = ce}{ts}{ts₁} {xs = xs} {ys = ys} {prg′} (DIP k {w} prg-dip) (↓-DIP prg-dip⇓ys)
  with bigstep1⇒smallstep {prg′ = mpush (H.take k xs) prg′} prg-dip prg-dip⇓ys
... | n , cstate≡ = suc (n + k) , trans (prog-step*-+ n k)
                                  (trans (cong (prog-step* k) cstate≡)
                                         (prog-step*-mpush k (H.take k xs) (length-take k ts (≤ᵇ⇒≤ k ts w))))
bigins⇒smallstep .(ITER _) ↓-ITER-[] = suc zero , refl
bigins⇒smallstep (ITER prg-iter) (↓-ITER-∷ prg-iter⇓xs iter↓ys)
  with bigstep1⇒smallstep prg-iter prg-iter⇓xs
... | n₁ , cstate≡₁
  with bigins⇒smallstep (ITER prg-iter) iter↓ys
... | n₂ , cstate≡₂ = (suc (n₁ + (suc n₂))) , (trans (prog-step*-+ n₁ (suc n₂)) (trans (cong (prog-step* (suc n₂)) cstate≡₁) cstate≡₂))
bigins⇒smallstep (IF-NONE prg-none _) (↓-IF-NONE prg-none⇓ys)
  with bigstep1⇒smallstep prg-none prg-none⇓ys
... | n , cstate≡ = suc n , cstate≡
bigins⇒smallstep (IF-NONE _ prg-some) (↓-IF-SOME prg-some⇓ys)
  with bigstep1⇒smallstep prg-some prg-some⇓ys
... | n , cstate≡ = suc n , cstate≡


bigstep⇒smallstep .end ⤋-end = zero , refl
bigstep⇒smallstep (ins ; prg) (⤋-seq ins↓ys prg⤋zs)
  with bigins⇒smallstep {prg = prg} _ ins↓ys
... | n₁ , cstate≡₁ 
  with bigstep⇒smallstep _ prg⤋zs
... | n₂ , cstate≡₂ = (n₁ + n₂) , trans (prog-step*-+ n₁ n₂) (trans (cong (prog-step* n₂) cstate≡₁) cstate≡₂)
bigstep⇒smallstep .(MPUSH1 _ ∙ _) (⤋-shadow ↓-MPUSH1 prg⤋ys)
  with bigstep⇒smallstep _ prg⤋ys
... | n , cstate≡ = suc n , cstate≡


bigstep1⇒smallstep .end ⇓-end = zero , refl
bigstep1⇒smallstep (ins ; prg) (⇓-seq ins↓xs′ prg⇓ys)
  with bigins⇒smallstep ins ins↓xs′
... | n₁ , cstate≡₁
  with bigstep1⇒smallstep prg prg⇓ys
... | n₂ , cstate≡₂ = (n₁ + n₂) , (trans (prog-step*-+ n₁ n₂) (trans (cong (prog-step* n₂) cstate≡₁) cstate≡₂))
