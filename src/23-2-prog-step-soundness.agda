
module 23-2-prog-step-soundness  where

import 00-All-Utilities as H

open import 01-Types
open import 02-Functions-Interpretations
open import 03-2-concrete-execution
open import 11-abstract-representation-and-weakening
open import 12-2-abstract-execution-accessories-and-weakening
open import 13-2-abstract-Prog-state-execution
open import 21-2-Prog-state-modeling
open import 22-2-P-s-m-weakening

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym)

open import Data.Nat.Base
open import Data.List.Base hiding ([_])
open import Data.List.Relation.Unary.All using (All; _∷_; [])
open import Data.Maybe.Base
open import Data.Product
open import Data.Sum
open import Data.Unit using (⊤; tt)

soundness : ∀ {Γ ro} γ αρ ρ → modρ {ro} {Γ} γ αρ ρ
          → ∃[ Γ` ] ∃[ γ` ] mod⊎ρ {Γ = Γ` ++ Γ} (γ` +I+ γ) (αprog-step αρ) (prog-step ρ)

soundness γ (state αen end r`VM Φ)
            (state en  end rSI tt)
            mρ@(modρ⟨ _ , _ , _ , _ ⟩)
  = _ , [I] , _ , 0∈ , mρ

soundness γ (state αen (enf `AMOUNT ; aprg) r`VM Φ)
            (state en  (enf `AMOUNT ; cprg) rSI tt)
            (modρ⟨ mE@(mβ , refl , refl , refl , refl) , mrS , (refl , refl , mPRG) , mΦ ⟩)
  = _ , [I] , _ , 0∈ , (modρ⟨ mE , (refl , mrS) , mPRG , mΦ ⟩)

soundness γ (state αen (enf `BALANCE ; aprg) r`VM Φ)
            (state en  (enf `BALANCE ; cprg) rSI tt)
            (modρ⟨ mE@(mβ , refl , refl , refl , refl) , mrS , (refl , refl , mPRG) , mΦ ⟩)
  = _ , [I] , _ , 0∈ , (modρ⟨ mE , (refl , mrS) , mPRG , mΦ ⟩)

soundness γ (state αen (enf (`CONTRACT P) ; aprg) (adr∈ ∷ r`VM) Φ)
            (state en (.enf (`CONTRACT P) ; cprg) (adr ∷ rSI)  tt)
            (modρ⟨ mE , (refl , mrS) , (refl , refl , mPRG) , mΦ ⟩)
  = [ option (contract P) ] , [ appcontract P en adr ]
  , _ , 0∈ , modρ⟨ wkmodE mE , (refl , wkmodS mrS) , wkmodprg mPRG , wkmodΦ mΦ ⟩


soundness γ (state αen (fct (D1 x) ; aprg) r`VM Φ)
            (state en  (.fct (D1 x) ; cprg) rSI tt)
            (modρ⟨ mE , mrS , (refl , refl , mPRG) , mΦ ⟩)
  with modS++ r`VM rSI mrS
... | mtop , mbot = _ , appD1 x (Itop rSI) ∷ [I] , _ , 0∈ , (refl ,
    wkmodE mE , wkmodprg mPRG , (refl , wkmodS mbot) , 
    cong (appD1 x) (trans (sym (mod`IMI mtop))
                          (wk`IMI {γ` = appD1 x (Itop rSI) ∷ [I]})) ,
    wkmodΦ mΦ)

soundness γ (state αen (fct (Dm `UNPAIR) ; aprg) (     p∈ ∷ r`VM) Φ)
            (state en  (fct (Dm `UNPAIR) ; cprg) ((x , y) ∷ rSI) tt)
            (modρ⟨ mE , (refl , mrS) , (refl , refl , mPRG) , mΦ ⟩)
  = _ , x ∷ y ∷ [I] , _ , 0∈ , (refl , wkmodE mE , wkmodprg mPRG ,
    (refl , refl , wkmodS mrS) , (refl , refl , wkmodΦ mΦ))

soundness γ (state αen (fct (Dm `SWAP) ; aprg) (x∈ ∷ y∈ ∷ r`VM) Φ)
            (state en  (fct (Dm `SWAP) ; cprg) (x  ∷ y  ∷ rSI) tt)
            (modρ⟨ mE , (refl , refl , mrS) , (refl , refl , mPRG) , mΦ ⟩)
  = _ , [I] , _ , 0∈ , (refl , mE , mPRG , (refl , refl , mrS) , mΦ)

soundness γ (state αen (fct (Dm `DUP) ; aprg) (x∈ ∷ r`VM) Φ)
            (state en (fct (Dm `DUP) ; cprg) (x  ∷ rSI) tt)
             (refl , mE , (refl , refl , mPRG) , (refl , mrS) , mRest)
  = _ , [I] , _ , 0∈ , (refl , mE , mPRG , (refl , refl , mrS) , mRest)

soundness γ (state αen (fct (`PUSH aP x) ; aprg) r`VM Φ)
            (state en  (fct (`PUSH cP x) ; cprg) rSI tt)
            (modρ⟨ mE , mrS , (refl , refl , mPRG) , mΦ ⟩)
  = _ , createγ aP x , _ , 0∈ , (refl , wkmodE mE , wkmodprg mPRG ,
    (trans (val∈wk {γ = createγ aP x}) (val0∈exΓ aP x) , wkmodS mrS) ,
    (modΦwk (modunfoldΦ aP x) +modΦ+ wkmodΦ mΦ) )

soundness γ (state αen (DROP ; aprg) (x∈ ∷ r`VM) Φ)
            (state en  (DROP ; cprg) (x  ∷ rSI) tt)
            (refl , mE , (refl , refl , mPRG) , (refl , mrS) , mRest)
  = _ , [I] , _ , 0∈ , (refl , mE , mPRG , mrS , mRest)


soundness γ (state αen (ITER x ; aprg) (l∈ ∷ r`VM) Φ)
            (state en (.ITER x ; cprg) ([] ∷ rSI) tt)
            (modρ⟨ mE , (l≡ , mrS) , (refl , refl , mPRG) , mΦ ⟩)
  = _ , [I] , _ , 0∈ , modρ⟨ mE , mrS , mPRG , (l≡ , mΦ) ⟩

soundness γ (state αen (ITER x ; aprg) (l∈ ∷ r`VM) Φ)
            (state en (.ITER x ; cprg) (( e ∷ l ) ∷ rSI) tt)
            (modρ⟨ mE , (l≡ , mrS) , (refl , refl , mPRG) , mΦ ⟩)
  = _ , e ∷ l ∷ [I] , _ , 1∈ ,
    modρ⟨ wkmodE mE , (refl , wkmodS mrS) , modprg-extend x (refl , refl , (refl , refl , wkmodprg mPRG)) , (l≡ , wkmodΦ mΦ) ⟩

soundness γ (state αen (DIP n x ; aprg) r`VM Φ)
            (state en (.DIP n x ; cprg) rSI tt)
            (modρ⟨ mE , mrS , (refl , refl , mPRG) , mΦ ⟩)
  = _ , [I] , _ , 0∈ , (refl , mE , modprg-extend x (modprg-mpush (modtake n r`VM rSI mrS) mPRG) ,
    moddrop n r`VM rSI mrS , mΦ)

soundness γ (state αen (IF-NONE thn els ; aprg) (o∈ ∷ r`VM) Φ)
            (state en (.IF-NONE thn els ; cprg) (just x ∷ rSI) tt)
            (modρ⟨ mE , (o≡ , mrS) , (refl , refl , mPRG) , mΦ ⟩)
  = _ , x ∷ [I] , _ , 1∈ , (refl , wkmodE mE , modprg-extend els (wkmodprg mPRG) ,
    (refl , wkmodS mrS) , (o≡ , wkmodΦ mΦ))

soundness γ (state αen (IF-NONE thn els ; aprg) (o∈ ∷ r`VM) Φ)
            (state en (.IF-NONE thn els ; cprg) (nothing ∷ rSI) tt)
            (modρ⟨ mE , (o≡ , mrS) , (refl , refl , mPRG) , mΦ ⟩)
  = _ , [I] , _ , 0∈ , (refl , mE , modprg-extend thn mPRG , mrS , (o≡ , mΦ))

soundness γ (state αen (`MPUSH1 x ∙ aprg) r`VM Φ)
            (state en  (`MPUSH1 y ∙ cprg) rSI tt)
            (modρ⟨ mE , mrS , (refl , mv-xy , mPRG) , mΦ ⟩)
  = -, [] , _ , 0∈ ,
    modρ⟨ mE , (mv-xy , mrS) , mPRG , mΦ ⟩


{-
soundness γ αρ ρ mρ = {!!} , {!!} , {!!} , _ , {!!} , {!!}
-}

