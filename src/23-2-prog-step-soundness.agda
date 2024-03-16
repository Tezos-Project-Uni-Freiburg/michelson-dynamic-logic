
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

soundness : ∀ {Γ ro so} γ αρ ρ → modρ {ro} {so} {Γ} γ αρ ρ
          → ∃[ Γ` ] ∃[ γ` ] mod⊎ρ {Γ = Γ` ++ Γ} (γ` +I+ γ) (αprog-step αρ) (prog-step ρ)

soundness γ (state αen end rVM sVM Φ)
            (state en .end rSI sSI tt)
            mρ@(modρ⟨ _ , _ , _ , _ ⟩)
  = _ , [I] , _ , 0∈ , mρ

soundness γ (state αen (enf AMOUNT ; prg) rVM sVM Φ)
            (state en .(enf AMOUNT ; prg) rSI sSI tt)
            (modρ⟨ mE@(mβ , refl , refl , refl , refl) , mrS , msS , mΦ ⟩)
  = _ , [I] , _ , 0∈ , (modρ⟨ mE , (refl , mrS) , msS , mΦ ⟩)

soundness γ (state αen (enf BALANCE ; prg) rVM sVM Φ)
            (state en .(enf BALANCE ; prg) rSI sSI tt)
            (modρ⟨ mE@(mβ , refl , refl , refl , refl) , mrS , msS , mΦ ⟩)
  = _ , [I] , _ , 0∈ , (modρ⟨ mE , (refl , mrS) , msS , mΦ ⟩)

soundness γ (state αen (enf (CONTRACT P) ; prg) (adr∈ ∷ rVM) sVM Φ)
            (state en .(enf (CONTRACT P) ; prg) (adr ∷ rSI) sSI tt)
            (modρ⟨ mE , (refl , mrS) , msS , mΦ ⟩)
  = [ option (contract P) ] , (appcontract P en adr ∷ [I])
  , _ , 0∈ , (refl , refl , wkmodE mE , refl ,
             (refl , wkmodS mrS) , wkmodS msS , wkmodΦ mΦ)

soundness γ (state αen (fct (D1 x) ; prg) rVM sVM Φ)
            (state en .(fct (D1 x) ; prg) rSI sSI tt)
            (modρ⟨ mE , mrS , msS , mΦ ⟩)
  with modS++ rVM rSI mrS
... | mtop , mbot = _ , appD1 x (Itop rSI) ∷ [I] , _ , 0∈ , (refl , refl ,
    wkmodE mE , refl , (refl , wkmodS mbot) , wkmodS msS ,
    cong (appD1 x) (trans (sym (modIMI mtop))
                          (wkIMI {γ` = appD1 x (Itop rSI) ∷ [I]})) ,
    wkmodΦ mΦ)

soundness γ (state αen (fct (Dm UNPAIR) ; prg) (     p∈ ∷ rVM) sVM Φ)
            (state en .(fct (Dm UNPAIR) ; prg) ((x , y) ∷ rSI) sSI tt)
            (modρ⟨ mE , (refl , mrS) , msS , mΦ ⟩)
  = _ , x ∷ y ∷ [I] , _ , 0∈ , (refl , refl , wkmodE mE , refl ,
    (refl , refl , wkmodS mrS) , wkmodS msS , (refl , refl , wkmodΦ mΦ))

soundness γ (state αen (fct (Dm SWAP) ; prg) (x∈ ∷ y∈ ∷ rVM) sVM Φ)
            (state en .(fct (Dm SWAP) ; prg) (x  ∷ y  ∷ rSI) sSI tt)
            (modρ⟨ mE , (refl , refl , mrS) , msS , mΦ ⟩)
  = _ , [I] , _ , 0∈ , (refl , refl , mE , refl , (refl , refl , mrS) , msS , mΦ)

soundness γ (state αen (fct (Dm DUP) ; prg) (x∈ ∷ rVM) sVM Φ)
            (state en .(fct (Dm DUP) ; prg) (x  ∷ rSI) sSI tt)
             (refl , refl , mE , refl , (refl , mrS) , mRest)
  = _ , [I] , _ , 0∈ , (refl , refl , mE , refl , (refl , refl , mrS) , mRest)

soundness γ (state αen (fct (PUSH P x) ; prg) rVM sVM Φ)
            (state en .(fct (PUSH P x) ; prg) rSI sSI tt)
            (modρ⟨ mE , mrS , msS , mΦ ⟩)
  = _ , createγ P x , _ , 0∈ , (refl , refl , wkmodE mE , refl ,
    (trans (val∈wk {γ = createγ P x}) (val0∈exΓ P x) , wkmodS mrS) , wkmodS msS ,
    (modΦwk (modunfoldΦ P x) +modΦ+ wkmodΦ mΦ) )

soundness γ (state αen (DROP ; prg) (x∈ ∷ rVM) sVM Φ)
            (state en .(DROP ; prg) (x  ∷ rSI) sSI tt)
            (refl , refl , mE , refl , (refl , mrS) , mRest)
  = _ , [I] , _ , 0∈ , (refl , refl , mE , refl , mrS , mRest)

soundness γ (state αen (ITER x ; prg) (l∈ ∷ rVM) sVM Φ)
            (state en .(ITER x ; prg) (l  ∷ rSI) sSI tt)
            (modρ⟨ mE , (refl , mrS) , msS , mΦ ⟩)
  = _ , [I] , _ , 0∈ , (refl , refl , mE , refl , mrS , (refl , msS) , mΦ)

soundness γ (state αen (DIP n x ; prg) rVM sVM Φ)
            (state en .(DIP n x ; prg) rSI sSI tt)
            (modρ⟨ mE , mrS , msS , mΦ ⟩)
  = _ , [I] , _ , 0∈ , (refl , refl , mE , refl ,
    moddrop n rVM rSI mrS , modtake n rVM rSI mrS +modS+ msS , mΦ)

soundness γ (state αen (IF-NONE thn els ; prg) (o∈ ∷ rVM) sVM Φ)
            (state en .(IF-NONE thn els ; prg) (just x ∷ rSI) sSI tt)
            (modρ⟨ mE , (o≡ , mrS) , msS , mΦ ⟩)
  = _ , x ∷ [I] , _ , 1∈ , (refl , refl , wkmodE mE , refl ,
    (refl , wkmodS mrS) , wkmodS msS , (o≡ , wkmodΦ mΦ))

soundness γ (state αen (IF-NONE thn els ; prg) (o∈ ∷ rVM) sVM Φ)
            (state en .(IF-NONE thn els ; prg) (nothing ∷ rSI) sSI tt)
            (modρ⟨ mE , (o≡ , mrS) , msS , mΦ ⟩)
  = _ , [I] , _ , 0∈ , (refl , refl , mE , refl , mrS , msS , (o≡ , mΦ))

soundness γ (state αen (ITER' x ∙ prg) rVM (l∈ ∷ sVM) Φ)
            (state en .(ITER' x ∙ prg) rSI ([] ∷ sSI) tt)
            (modρ⟨ mE , mrS , (l≡ , msS) , mΦ ⟩)
  = _ , [I] , _ , 0∈ , (refl , refl , mE , refl , mrS , msS , (l≡ , mΦ))
  
soundness γ (state αen (ITER' x ∙ prg) rVM (l∈ ∷ sVM) Φ)
            (state en .(ITER' x ∙ prg) rSI ([ e // l ] ∷ sSI) tt)
            (modρ⟨ mE , mrS , (l≡ , msS) , mΦ ⟩)
  = _ , e ∷ l ∷ [I] , _ , 1∈ , (refl , refl , wkmodE mE , refl ,
    (refl , wkmodS mrS) , (refl , wkmodS msS) , (l≡ , wkmodΦ mΦ))

soundness γ (state αen (DIP' top ∙ prg) rVM sVM Φ)
            (state en .(DIP' top ∙ prg) rSI sSI tt)
            (modρ⟨ mE , mrS , msS , mΦ ⟩)  with modS++ sVM sSI msS
... | mtop , mbot = _ , [I] , _ , 0∈ , (refl , refl , mE , refl ,
    mtop +modS+ mrS , mbot , mΦ)


{-
soundness γ αρ ρ mρ = {!!} , {!!} , {!!} , _ , {!!} , {!!}
-}

