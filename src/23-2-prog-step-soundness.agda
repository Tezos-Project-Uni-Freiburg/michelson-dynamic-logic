
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

soundness γ (state αen end r`VM s`VM Φ)
            (state en .end r`SI s`SI tt)
            mρ@(modρ⟨ _ , _ , _ , _ ⟩)
  = _ , [I] , _ , 0∈ , mρ

soundness γ (state αen (enf `AMOUNT ; prg) r`VM s`VM Φ)
            (state en .(enf `AMOUNT ; prg) r`SI s`SI tt)
            (modρ⟨ mE@(mβ , refl , refl , refl , refl) , mrS , msS , mΦ ⟩)
  = _ , [I] , _ , 0∈ , (modρ⟨ mE , (refl , mrS) , msS , mΦ ⟩)

soundness γ (state αen (enf `BALANCE ; prg) r`VM s`VM Φ)
            (state en .(enf `BALANCE ; prg) r`SI s`SI tt)
            (modρ⟨ mE@(mβ , refl , refl , refl , refl) , mrS , msS , mΦ ⟩)
  = _ , [I] , _ , 0∈ , (modρ⟨ mE , (refl , mrS) , msS , mΦ ⟩)

soundness γ (state αen (enf (`CONTRACT P) ; prg) (adr∈ ∷ r`VM) s`VM Φ)
            (state en .(enf (`CONTRACT P) ; prg) (adr ∷ r`SI) s`SI tt)
            (modρ⟨ mE , (refl , mrS) , msS , mΦ ⟩)
  = [ option (contract P) ] , (appcontract P en adr ∷ [I])
  , _ , 0∈ , (refl , refl , wkmodE mE , refl ,
             (refl , wkmodS mrS) , wkmodS msS , wkmodΦ mΦ)

soundness γ (state αen (fct (D1 x) ; prg) r`VM s`VM Φ)
            (state en .(fct (D1 x) ; prg) r`SI s`SI tt)
            (modρ⟨ mE , mrS , msS , mΦ ⟩)
  with modS++ r`VM r`SI mrS
... | mtop , mbot = _ , appD1 x (Itop r`SI) ∷ [I] , _ , 0∈ , (refl , refl ,
    wkmodE mE , refl , (refl , wkmodS mbot) , wkmodS msS ,
    cong (appD1 x) (trans (sym (mod`IMI mtop))
                          (wk`IMI {γ` = appD1 x (Itop r`SI) ∷ [I]})) ,
    wkmodΦ mΦ)

soundness γ (state αen (fct (Dm `UNPAIR) ; prg) (     p∈ ∷ r`VM) s`VM Φ)
            (state en .(fct (Dm `UNPAIR) ; prg) ((x , y) ∷ r`SI) s`SI tt)
            (modρ⟨ mE , (refl , mrS) , msS , mΦ ⟩)
  = _ , x ∷ y ∷ [I] , _ , 0∈ , (refl , refl , wkmodE mE , refl ,
    (refl , refl , wkmodS mrS) , wkmodS msS , (refl , refl , wkmodΦ mΦ))

soundness γ (state αen (fct (Dm `SWAP) ; prg) (x∈ ∷ y∈ ∷ r`VM) s`VM Φ)
            (state en .(fct (Dm `SWAP) ; prg) (x  ∷ y  ∷ r`SI) s`SI tt)
            (modρ⟨ mE , (refl , refl , mrS) , msS , mΦ ⟩)
  = _ , [I] , _ , 0∈ , (refl , refl , mE , refl , (refl , refl , mrS) , msS , mΦ)

soundness γ (state αen (fct (Dm `DUP) ; prg) (x∈ ∷ r`VM) s`VM Φ)
            (state en .(fct (Dm `DUP) ; prg) (x  ∷ r`SI) s`SI tt)
             (refl , refl , mE , refl , (refl , mrS) , mRest)
  = _ , [I] , _ , 0∈ , (refl , refl , mE , refl , (refl , refl , mrS) , mRest)

soundness γ (state αen (fct (`PUSH P x) ; prg) r`VM s`VM Φ)
            (state en .(fct (`PUSH P x) ; prg) r`SI s`SI tt)
            (modρ⟨ mE , mrS , msS , mΦ ⟩)
  = _ , createγ P x , _ , 0∈ , (refl , refl , wkmodE mE , refl ,
    (trans (val∈wk {γ = createγ P x}) (val0∈exΓ P x) , wkmodS mrS) , wkmodS msS ,
    (modΦwk (modunfoldΦ P x) +modΦ+ wkmodΦ mΦ) )

soundness γ (state αen (`DROP ; prg) (x∈ ∷ r`VM) s`VM Φ)
            (state en .(`DROP ; prg) (x  ∷ r`SI) s`SI tt)
            (refl , refl , mE , refl , (refl , mrS) , mRest)
  = _ , [I] , _ , 0∈ , (refl , refl , mE , refl , mrS , mRest)

soundness γ (state αen (`ITER x ; prg) (l∈ ∷ r`VM) s`VM Φ)
            (state en .(`ITER x ; prg) (l  ∷ r`SI) s`SI tt)
            (modρ⟨ mE , (refl , mrS) , msS , mΦ ⟩)
  = _ , [I] , _ , 0∈ , (refl , refl , mE , refl , mrS , (refl , msS) , mΦ)

soundness γ (state αen (`DIP n x ; prg) r`VM s`VM Φ)
            (state en .(`DIP n x ; prg) r`SI s`SI tt)
            (modρ⟨ mE , mrS , msS , mΦ ⟩)
  = _ , [I] , _ , 0∈ , (refl , refl , mE , refl ,
    moddrop n r`VM r`SI mrS , modtake n r`VM r`SI mrS +modS+ msS , mΦ)

soundness γ (state αen (`IF-NONE thn els ; prg) (o∈ ∷ r`VM) s`VM Φ)
            (state en .(`IF-NONE thn els ; prg) (just x ∷ r`SI) s`SI tt)
            (modρ⟨ mE , (o≡ , mrS) , msS , mΦ ⟩)
  = _ , x ∷ [I] , _ , 1∈ , (refl , refl , wkmodE mE , refl ,
    (refl , wkmodS mrS) , wkmodS msS , (o≡ , wkmodΦ mΦ))

soundness γ (state αen (`IF-NONE thn els ; prg) (o∈ ∷ r`VM) s`VM Φ)
            (state en .(`IF-NONE thn els ; prg) (nothing ∷ r`SI) s`SI tt)
            (modρ⟨ mE , (o≡ , mrS) , msS , mΦ ⟩)
  = _ , [I] , _ , 0∈ , (refl , refl , mE , refl , mrS , msS , (o≡ , mΦ))

soundness γ (state αen (`ITER' x ∙ prg) r`VM (l∈ ∷ s`VM) Φ)
            (state en .(`ITER' x ∙ prg) r`SI ([] ∷ s`SI) tt)
            (modρ⟨ mE , mrS , (l≡ , msS) , mΦ ⟩)
  = _ , [I] , _ , 0∈ , (refl , refl , mE , refl , mrS , msS , (l≡ , mΦ))
  
soundness γ (state αen (`ITER' x ∙ prg) r`VM (l∈ ∷ s`VM) Φ)
            (state en .(`ITER' x ∙ prg) r`SI ([ e // l ] ∷ s`SI) tt)
            (modρ⟨ mE , mrS , (l≡ , msS) , mΦ ⟩)
  = _ , e ∷ l ∷ [I] , _ , 1∈ , (refl , refl , wkmodE mE , refl ,
    (refl , wkmodS mrS) , (refl , wkmodS msS) , (l≡ , wkmodΦ mΦ))

soundness γ (state αen (`DIP' top ∙ prg) r`VM s`VM Φ)
            (state en .(`DIP' top ∙ prg) r`SI s`SI tt)
            (modρ⟨ mE , mrS , msS , mΦ ⟩)  with modS++ s`VM s`SI msS
... | mtop , mbot = _ , [I] , _ , 0∈ , (refl , refl , mE , refl ,
    mtop +modS+ mrS , mbot , mΦ)


{-
soundness γ αρ ρ mρ = {!!} , {!!} , {!!} , _ , {!!} , {!!}
-}

