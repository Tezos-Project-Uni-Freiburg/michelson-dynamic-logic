module 03-3-bigstep-execution where

open import Data.Empty
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

--! Bigstep >

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

variable
  tx : Type
  txs tys : List Type
  x : ⟦ tx ⟧
  xs : Int txs
  ys : Int tys
  ce : CEnvironment
  ri : List Type

--! Configuration
record Configuration (ri : Stack) : Set where
  constructor Conf
  field cenv : CEnvironment ; stk  : Int ri


--! Judgment
data [_,_]⇓_ : Configuration ri → Program ri ro → Int ro → Set

data [_,_]⤋_ : Configuration ri → ShadowProg{⟦_⟧} ri ro → Int ro → Set

data [_,_]↓′_ : Configuration ri → ShadowInst ri ro → Int ro → Set where
  ↓-MPUSH1 : ∀ {t txs ce}  {x : ⟦ t ⟧} {xs : Int txs}
    → [ Conf ce xs , MPUSH1 x ]↓′ (x ∷ xs)

data [_,_]↓_ : Configuration ri → Instruction ri ro → Int ro → Set where
  ↓-fct : ∀{args}{result}{ft : func-type args result} {xs : Int (args ++ txs)}
    → [ Conf ce xs , fct ft ]↓ (app-fct ft (H.front xs) H.++ H.rest xs)
  ↓-enf : ∀{args}{result}{ef : env-func args result} {xs : Int (args ++ txs)}
    → [ Conf ce xs , enf ef ]↓ (app-enf ef ce (H.front xs) ∷ H.rest xs)
  ↓-DROP : ∀ {t txs ce} {x : ⟦ t ⟧} {xs : Int txs}
    → [ Conf ce (x ∷ xs) , DROP ]↓ xs

--! DIP
  ↓-DIP : ∀ {n} {q : T (n ≤ᵇ length txs)} {p-dip : Program (drop n txs) tys}
    → [ Conf ce (H.drop n xs) , p-dip ]⇓ ys
    -------------------------------------------------------
    → [ Conf ce xs , DIP n {q} p-dip ]↓ (H.take n xs H.++ ys)

--! IterNil
  ↓-ITER-NIL : ∀ {p-iter : Program (t ∷ txs) txs}
    -----------------------------------------
    → [ Conf ce ([] ∷ xs) , ITER p-iter ]↓ xs

--! IterCons
  ↓-ITER-CONS : ∀ {v : ⟦ t ⟧}{vs : ⟦ list t ⟧} {xs ys zs : Int txs} {p-iter : Program (t ∷ txs) txs}
    → [ Conf ce (v ∷ xs) , p-iter ]⇓ ys
    → [ Conf ce (vs ∷ ys) , ITER p-iter ]↓ zs
    ----------------------------------------------
    → [ Conf ce ((v ∷ vs) ∷ xs) , ITER p-iter ]↓ zs

--! IfNone
  ↓-IF-NONE : ∀ {p-none : Program txs tys} {p-some : Program (tx ∷ txs) tys}
    → [ Conf ce xs , p-none ]⇓ ys
    --------------------------------------------------------
    → [ Conf ce (nothing ∷ xs) , IF-NONE p-none p-some ]↓ ys

--! IfSome
  ↓-IF-SOME : ∀ {p-none : Program txs tys} {p-some : Program (tx ∷ txs) tys}
    → [ Conf ce (x ∷ xs) , p-some ]⇓ ys
    --------------------------------------------------------
    → [ Conf ce (just x ∷ xs) , IF-NONE p-none p-some ]↓ ys
  
data [_,_]⇓_ where

  ⇓-end : ∀ {txs ce} {xs : Int txs}
    → [ Conf ce xs , end ]⇓ xs
  ⇓-seq : ∀ {txs txs₁ txs₂ ce} {xs : Int txs} {ys : Int txs₁} {zs : Int txs₂} {ins : Instruction txs txs₁} {prg : Program txs₁ txs₂}
    → [ Conf ce xs , ins ]↓ ys
    → [ Conf ce ys , prg ]⇓ zs
    → [ Conf ce xs , ins ; prg ]⇓ zs


data [_,_]⤋_ where

  ⤋-end : ∀ {txs ce} {xs : Int txs}
    → [ Conf ce xs , end ]⤋ xs
  ⤋-seq : ∀ {txs txs₁ txs₂ ce} {xs : Int txs} {ys : Int txs₁} {zs : Int txs₂} {ins : Instruction txs txs₁} {prg : ShadowProg txs₁ txs₂}
    → [ Conf ce xs , ins ]↓ ys
    → [ Conf ce ys , prg ]⤋ zs
    → [ Conf ce xs , ins ; prg ]⤋ zs
  ⤋-shadow : ∀ {txs txs₁ txs₂ ce} {xs : Int txs} {ys : Int txs₁} {zs : Int txs₂} {ins : ShadowInst txs txs₁} {prg : ShadowProg txs₁ txs₂}
    → [ Conf ce xs , ins ]↓′ ys
    → [ Conf ce ys , prg ]⤋ zs
    → [ Conf ce xs , ins ∙ prg ]⤋ zs

-- prove soundness: if we make a prog-step, then the result remains the same.

concat-⤋ : ∀ {ce txs txs₁ txs₂} {xs : Int txs}{xs₁ : Int txs₁}{xs₂ : Int txs₂} {prg₁}
  → ∀ prg
  → [ Conf ce xs , prg ]⇓ xs₁
  → [ Conf ce xs₁ , prg₁ ]⤋ xs₂
  → [ Conf ce xs , prg ;∙ prg₁ ]⤋ xs₂
concat-⤋ end ⇓-end prg₁⤋xs₂ = prg₁⤋xs₂
concat-⤋ (ins ; prg) (⇓-seq ↓-ins prg⤋xs₁) prg₁⤋xs₂ = ⤋-seq ↓-ins (concat-⤋ prg prg⤋xs₁ prg₁⤋xs₂)

mpush1-⤋ :  ∀ {ce t txs′} (x : ⟦_⟧ t) {xs′ : Int txs′} {ys : Int ro} {prg}
  → [ Conf ce (x ∷ xs′) , prg ]⤋ ys
  → [ Conf ce xs′ , MPUSH1 x ∙ prg ]⤋ ys
mpush1-⤋ x prg⤋ys = ⤋-shadow ↓-MPUSH1 prg⤋ys

mpush-⤋ : ∀ {ce txs txs′} (xs : Int txs) {xs′ : Int txs′} {ys : Int ro} {prg}
  → [ Conf ce (xs H.++ xs′) , prg ]⤋ ys
  → [ Conf ce xs′ , mpush xs prg ]⤋ ys
mpush-⤋ [I] prg⤋ys = prg⤋ys
mpush-⤋ (x ∷ xs) prg⤋ys = mpush-⤋ xs (mpush1-⤋ x prg⤋ys)

⤋-mpush1 :  ∀ {ce t txs′} (x : ⟦_⟧ t) {xs′ : Int txs′} {ys : Int ro} {prg}
  → [ Conf ce xs′ , MPUSH1 x ∙ prg ]⤋ ys
  → [ Conf ce (x ∷ xs′) , prg ]⤋ ys
⤋-mpush1 x (⤋-shadow ↓-MPUSH1 mp⤋) = mp⤋

⤋-mpush : ∀ {ce txs txs′} (xs : Int txs) {xs′ : Int txs′} {ys : Int ro} {prg}
  → [ Conf ce xs′ , mpush xs prg ]⤋ ys
  → [ Conf ce (xs H.++ xs′) , prg ]⤋ ys
⤋-mpush [I] prg⤋ = prg⤋
⤋-mpush ([ px ]++ xs) prg⤋ = ⤋-mpush1 px (⤋-mpush xs prg⤋)


smallstep-soundness-⤋ : ∀ {ce txs txs′} {xs : Int txs} {xs′ : Int txs′} {ys : Int ro} (prg : ShadowProg txs ro) {prg′ : ShadowProg txs′ ro}
  → [ Conf ce xs , prg ]⤋ ys
  → prog-step (cstate ce prg xs) ≡ cstate ce prg′ xs′
  → [ Conf ce xs′ , prg′ ]⤋ ys
smallstep-soundness-⤋ end prg⤋ys refl = prg⤋ys
smallstep-soundness-⤋ (enf x ; prg) (⤋-seq ↓-enf prg⤋ys) refl = prg⤋ys
smallstep-soundness-⤋ (fct ft ; prg) (⤋-seq ↓-fct prg⤋ys) refl = prg⤋ys
smallstep-soundness-⤋ (DROP ; prg) (⤋-seq ↓-DROP prg⤋ys) refl = prg⤋ys
smallstep-soundness-⤋ (ITER p-iter ; prg) (⤋-seq ↓-ITER-NIL prg⤋ys) refl = prg⤋ys
smallstep-soundness-⤋ (ITER p-iter ; prg) (⤋-seq (↓-ITER-CONS p-iter⤋x₁ iter-p-iter⤋x₂) prg⤋ys) refl = concat-⤋ p-iter p-iter⤋x₁ (⤋-shadow ↓-MPUSH1 (⤋-seq iter-p-iter⤋x₂ prg⤋ys))
smallstep-soundness-⤋ (DIP n p-dip ; prg) (⤋-seq (↓-DIP p-dip⤋ys₁) prg⤋ys) refl = concat-⤋ p-dip p-dip⤋ys₁ (mpush-⤋ _ prg⤋ys)
smallstep-soundness-⤋ (IF-NONE p-none p-some ; prg) (⤋-seq (↓-IF-NONE p-none⤋ys₁) prg⤋ys) refl = concat-⤋ p-none p-none⤋ys₁ prg⤋ys
smallstep-soundness-⤋ (IF-NONE p-none p-some ; prg) (⤋-seq (↓-IF-SOME p-some⤋ys₁) prg⤋ys) refl = concat-⤋ p-some p-some⤋ys₁ prg⤋ys
smallstep-soundness-⤋ (MPUSH1 x ∙ prg) (⤋-shadow ↓-MPUSH1 prg⤋ys) refl = prg⤋ys

----------------------------------------
prog-step*-mpush : ∀ {ce} {txs}{txs′} k (xs : Int txs) {xs′ : Int txs′} {prg : ShadowProg (txs ++ txs′) ro} (p : length txs ≡ k) 
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

--! ToSmallstep
bigstep⇒smallstep : ∀ (prg : ShadowProg txs tys)
  → [ Conf ce xs , prg ]⤋ ys
  → ∃[ n ] prog-step* n (cstate ce prg xs) ≡ cstate ce end ys

bigins⇒smallstep : ∀ {prg : ShadowProg tys ro}
  → (ins : Instruction txs tys)
  → [ Conf ce xs , ins ]↓ ys
  → ∃[ n ] prog-step* n (cstate ce (ins ; prg) xs) ≡ cstate ce prg ys

bigstep1⇒smallstep : ∀  {prg′  : ShadowProg tys ro} (prg : Program txs tys)
  → [ Conf ce xs , prg ]⇓ ys
  → ∃[ n ] prog-step* n (cstate ce (prg ;∙ prg′) xs) ≡ cstate ce prg′ ys

bigins⇒smallstep (fct _) ↓-fct = suc zero , refl
bigins⇒smallstep (enf _) ↓-enf = suc zero , refl
bigins⇒smallstep .DROP ↓-DROP = suc zero , refl
bigins⇒smallstep {txs = txs} {xs = xs} {ys = ys} {prg′} (DIP k {w} p-dip) (↓-DIP p-dip⇓ys)
  with bigstep1⇒smallstep {prg′ = mpush (H.take k xs) prg′} p-dip p-dip⇓ys
... | n , cstate≡ = suc (n + k) , trans (prog-step*-+ n k)
                                  (trans (cong (prog-step* k) cstate≡)
                                         (prog-step*-mpush k (H.take k xs) (length-take k txs (≤ᵇ⇒≤ k txs w))))
bigins⇒smallstep .(ITER _) ↓-ITER-NIL = suc zero , refl
bigins⇒smallstep (ITER p-iter) (↓-ITER-CONS p-iter⇓xs iter↓ys)
  with bigstep1⇒smallstep p-iter p-iter⇓xs
... | n₁ , cstate≡₁
  with bigins⇒smallstep (ITER p-iter) iter↓ys
... | n₂ , cstate≡₂ = (suc (n₁ + (suc n₂))) , (trans (prog-step*-+ n₁ (suc n₂)) (trans (cong (prog-step* (suc n₂)) cstate≡₁) cstate≡₂))
bigins⇒smallstep (IF-NONE p-none _) (↓-IF-NONE p-none⇓ys)
  with bigstep1⇒smallstep p-none p-none⇓ys
... | n , cstate≡ = suc n , cstate≡
bigins⇒smallstep (IF-NONE _ p-some) (↓-IF-SOME p-some⇓ys)
  with bigstep1⇒smallstep p-some p-some⇓ys
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

----------------------------------------------------------------------

⤋-;∙-decompose : ∀ {tzs} (p1 : Program txs tzs) {p2 : ShadowProg tzs tys}
  → [ Conf ce xs , p1 ;∙ p2 ]⤋ ys
  → ∃[ zs ] ([ Conf ce xs , p1 ]⇓ zs × [ Conf ce zs , p2 ]⤋ ys)
⤋-;∙-decompose {xs = xs} end p1p2⤋ys = xs , (⇓-end , p1p2⤋ys)
⤋-;∙-decompose (ins ; p1) (⤋-seq ins↓zs p1p2⤋ys)
  with ⤋-;∙-decompose p1 p1p2⤋ys
... | zs , p1⇓zs , p2⤋ys = zs , ((⇓-seq ins↓zs p1⇓zs) , p2⤋ys)


--! FromSmallstep
smallstep⇒bigstep : ∀ n → (prg : ShadowProg txs tys) → {xs : Int txs} {ys : Int tys}
  → prog-step* n (cstate ce prg xs) ≡ cstate ce end ys
  → [ Conf ce xs , prg ]⤋ ys

smallstep⇒bigstep zero end refl = ⤋-end
smallstep⇒bigstep (suc n) end eq = smallstep⇒bigstep n end eq
smallstep⇒bigstep (suc n) (enf ef ; prg) eq = ⤋-seq ↓-enf (smallstep⇒bigstep n prg eq)
smallstep⇒bigstep (suc n) (fct ft ; prg) {xs = xs} eq = ⤋-seq ↓-fct (smallstep⇒bigstep n prg eq)
smallstep⇒bigstep (suc n) (DROP ; prg) {xs = _ ∷ _} eq = ⤋-seq ↓-DROP (smallstep⇒bigstep n prg eq)
smallstep⇒bigstep (suc n) (ITER ip ; prg) {xs = [] ∷ xs} eq = ⤋-seq ↓-ITER-NIL (smallstep⇒bigstep n prg eq)
smallstep⇒bigstep (suc n) (ITER ip ; prg) {xs = (b ∷ bs) ∷ xs} eq
  with smallstep⇒bigstep n (ip ;∙ (MPUSH1 bs ∙ (ITER ip ; prg))) eq
... | ih
  with ⤋-;∙-decompose ip ih
... | zs , ip⇓ , rest⤋
  with ⤋-mpush1 bs rest⤋
... | ⤋-seq ip↓ prg⤋ = ⤋-seq (↓-ITER-CONS ip⇓ ip↓) prg⤋
smallstep⇒bigstep (suc n) (DIP k p-dip ; prg) {xs = xs} x
  with smallstep⇒bigstep n (p-dip ;∙ mpush (H.take k xs) prg) x
... | ih
  with ⤋-;∙-decompose p-dip ih
... | zs , p-dip⇓ , rest⤋ = ⤋-seq (↓-DIP p-dip⇓) (⤋-mpush (H.take k xs) rest⤋)
smallstep⇒bigstep (suc n) (IF-NONE p₁ p₂ ; prg) {xs = [ just x ]++ xs} eq
  with smallstep⇒bigstep n (p₂ ;∙ prg) eq
... | ih
  with ⤋-;∙-decompose p₂ ih
... | zs , p₂⇓ , rest⤋ = ⤋-seq (↓-IF-SOME p₂⇓) rest⤋
smallstep⇒bigstep (suc n) (IF-NONE p₁ p₂ ; prg) {xs = [ nothing ]++ xs} eq
  with smallstep⇒bigstep n (p₁ ;∙ prg) eq
... | ih
  with ⤋-;∙-decompose p₁ ih
... | zs , p₁⇓ , rest⤋ = ⤋-seq (↓-IF-NONE p₁⇓) rest⤋
smallstep⇒bigstep (suc n) (MPUSH1 x₁ ∙ prg) x
  with smallstep⇒bigstep n prg x
... | ih = ⤋-shadow ↓-MPUSH1 ih
