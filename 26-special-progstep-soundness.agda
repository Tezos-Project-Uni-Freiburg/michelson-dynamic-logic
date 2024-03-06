
module 26-special-progstep-soundness where

open import 01-Types
open import 02-Functions-Interpretations
open import 03-concrete-execution
open import 11-abstract-representation-and-weakening
open import 12-abstract-execution-accessories-and-weakening
open import 13-abstract-Prog-state-execution
open import 15-abstract-special-cases
open import 21-Prog-state-modeling
open import 22-P-s-m-weakening

open import Relation.Binary.PropositionalEquality.Core

open import Data.Nat renaming (_≟_ to _≟ₙ_)
open import Data.List.Base hiding ([_])
open import Data.Maybe.Base
open import Data.Product
open import Data.Sum

open import Data.List.Relation.Unary.All
open import Data.List.Relation.Unary.Any
open import Data.List.Membership.Propositional using (_∈_)

open import Relation.Nullary
open import Data.Empty
open import Data.Unit using (⊤; tt)


getInt≡Itop : ∀ {Γ γ top bot Φ} {Margs : Match Γ top} {rVM rSI}
            → modS {top ++ bot} {Γ} γ (Margs +M+ rVM) rSI
            → modΦ γ Φ
            → (MCargs : MatchConst Φ Margs)
            → getInt MCargs ≡ Itop rSI
getInt≡Itop {top = []} mrS mΦ [MC] = refl
getInt≡Itop {top = [ base _ // top ]} {rSI = _ ∷ rSI} (refl , mrS) mΦ (v∈=const ∷ MCargs)
  with modφ∈Φ v∈=const mΦ
... | refl rewrite getInt≡Itop mrS mΦ MCargs = refl

soundness : ∀ {Γ ro so γ αρ Γ` αρ`}
          → αρ-special αρ (Γ` , αρ`)
          → (ρ : Prog-state {ro} {so})
          → modρ {Γ} {ro} {so} γ αρ ρ
          → ∃[ γ` ] modρ (γ` +I+ γ) αρ` (prog-step ρ)

soundness (CAR φ∈Φ) (state en _ (p ∷ rSI) sSI)
          (refl , refl , mE , refl , (refl , mrS) , msS , mΦ)
  with modφ∈Φ φ∈Φ mΦ
... | p∈≡p rewrite p∈≡p = _ , refl , refl , mE , refl , (refl , mrS) , msS , mΦ

soundness (CDR φ∈Φ) (state en _ (p ∷ rSI) sSI)
          (refl , refl , mE , refl , (refl , mrS) , msS , mΦ)
  with modφ∈Φ φ∈Φ mΦ
... | p∈≡p rewrite p∈≡p = _ , refl , refl , mE , refl , (refl , mrS) , msS , mΦ

soundness (UNPAIR φ∈Φ) (state en _ (p ∷ rSI) sSI)
          (refl , refl , mE , refl , (refl , mrS) , msS , mΦ)
  with modφ∈Φ φ∈Φ mΦ
... | p∈≡p rewrite p∈≡p = _ , refl , refl , mE , refl , (refl , refl , mrS) , msS , mΦ

soundness (CTRn φ∈Φ ≡n) (state en _ (a ∷ rSI) sSI)
          (refl , refl , mE@(mβ , mErest) , refl , (refl , mrS) , msS , mΦ)
  with modφ∈Φ φ∈Φ mΦ | mβ a
... | refl | mMCa
  rewrite ≡n
  with Environment.accounts en a | mMCa
... | nothing | tt
  = (nothing ∷ [I]) , refl , refl , wkmodE mE , refl
  , (refl , wkmodS mrS) , wkmodS msS , (refl , wkmodΦ mΦ)

soundness (CTR¬p {p' = p'} φ∈Φ ≡j p≢p') (state en _ (a ∷ rSI) sSI)
          (refl , refl , mE@(mβ , mErest) , refl , (refl , mrS) , msS , mΦ)
  with modφ∈Φ φ∈Φ mΦ | mβ a
... | refl | mMCa
  rewrite ≡j
  with Environment.accounts en a | mMCa
... | just (p , s , c) | refl , mpC
  with p ≟ p'
... | yes refl = ⊥-elim (p≢p' refl)
... | no x
  = (nothing ∷ [I]) , refl , refl , wkmodE mE , refl
  , (refl , wkmodS mrS) , wkmodS msS , (refl , wkmodΦ mΦ)

soundness (CTRjp φ∈Φ ≡j) (state en _ (a ∷ rSI) sSI)
          (refl , refl , mE@(mβ , mErest) , refl , (refl , mrS) , msS , mΦ)
  with modφ∈Φ φ∈Φ mΦ | mβ a
... | refl | mMCa
  rewrite ≡j
  with Environment.accounts en a | mMCa
... | just (p , s , c) | refl , mpC
  with p ≟ p
... | yes refl
  = (a ∷ just a ∷ [I]) , refl , refl , wkmodE mE , refl
  , (refl , wkmodS mrS) , wkmodS msS , (refl , refl , wkmodΦ mΦ)
... | no x = ⊥-elim (x refl)

soundness (IF-Nn φ∈Φ) (state en _ (o ∷ rSI) sSI)
          (refl , refl , mE , refl , (refl , mrS) , msS , mΦ)
  with modφ∈Φ φ∈Φ mΦ
... | o∈≡o rewrite o∈≡o = _ , refl , refl , mE , refl , mrS , msS , mΦ

soundness (IF-Ns φ∈Φ) (state en _ (o ∷ rSI) sSI)
          (refl , refl , mE , refl , (refl , mrS) , msS , mΦ)
  with modφ∈Φ φ∈Φ mΦ
... | o∈≡o rewrite o∈≡o = _ , refl , refl , mE , refl , (refl , mrS) , msS , mΦ

soundness (ITER'n φ∈Φ) (state en _ rSI (l ∷ sSI))
          (refl , refl , mE , refl , mrS , (refl , msS) , mΦ)
  with modφ∈Φ φ∈Φ mΦ
... | o∈≡o rewrite o∈≡o = _ , refl , refl , mE , refl , mrS , msS , mΦ

soundness (ITER'c φ∈Φ) (state en _ rSI (l ∷ sSI))
          (refl , refl , mE , refl , mrS , (refl , msS) , mΦ)
  with modφ∈Φ φ∈Φ mΦ
... | o∈≡o rewrite o∈≡o = _ , refl , refl , mE , refl , (refl , mrS) , (refl , msS) , mΦ

soundness (app-bf {args = [ x ]++ args} {bf = bf} MCargs) (state en _ rSI sSI) (refl , refl , mE , refl , mrS , msS , mΦ) =
  [ appD1 bf (getInt MCargs) ] , refl , refl , wkmodE mE , refl , (cong (appD1 bf) (getInt≡Itop mrS mΦ MCargs) , wkmodS (modbot mrS)) , wkmodS msS , refl , wkmodΦ mΦ

{-
FOL-soundness mΦ (app-const-args {d1f = d1f} MCargs v∈=func)  with modφ∈Φ v∈=func mΦ
... | v∈≡func           = modφ∷=φ` v∈=func (trans v∈≡func (cong getvalue (cong (apply (impl (D1func d1f))) (IMIgetM≡getI MCargs mΦ)))) mΦ
-}

