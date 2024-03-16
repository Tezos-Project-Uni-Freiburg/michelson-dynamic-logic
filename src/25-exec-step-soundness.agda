
module 25-exec-step-soundness where

open import 01-Types
open import 02-Functions-Interpretations
open import 03-concrete-execution
open import 11-abstract-representation-and-weakening
open import 12-abstract-execution-accessories-and-weakening
open import 13-abstract-Prog-state-execution
open import 14-abstract-Exec-state-execution
open import 21-Prog-state-modeling
open import 22-P-s-m-weakening
open import 23-prog-step-soundness renaming (soundness to ρ-sound)
open import 24-Exec-state-modeling

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality.Core

open import Data.Nat renaming (_≟_ to _≟ₙ_) hiding (_/_)
open import Data.List.Base hiding ([_]; unfold)
open import Data.Maybe.Base
open import Data.Product
open import Data.Sum hiding ([_,_]; map)

open import Data.List.Relation.Unary.All
open import Data.List.Relation.Unary.Any
open import Data.List.Membership.Propositional using (_∈_)

open import Data.List.Properties
open import Data.Product.Properties

open import Data.Unit using (⊤; tt)

soundness : ∀ {Γ : Context} γ ασ σ → modσ {Γ} γ ασ σ
          → Exec-state.MPstate σ ≡ nothing
          ⊎ ∃[ Γ` ] ∃[ γ` ] mod⊎σ {Γ` ++ Γ} (γ` +I+ γ) (αexec-step ασ) (exec-step σ)

soundness γ (αexc αccounts (inj₂ Φ)  αpending)
             (exc accounts nothing    pending) mσ = inj₁ refl

soundness γ
  (αexc αccounts
        (inj₁ (αpr {ss = s} αself αsender (αstate
          (αenv _  cadr  sadr blc∈ amn∈) end (no,ns∈ ∷ [M]) [M] Φ)))
        αpending)
   (exc accounts
        (just (pr self sender (state
           (env _ .cadr .sadr blc  amn) .end ((n-ops , n-stor) ∷ [I]) [I])))
        pending)
   ( mβ
   , ( refl , refl , refl , refl
     , (refl , refl , refl , refl , refl) , (refl , refl , refl , refl , refl)
     , refl , refl , (_ , refl , refl , refl , refl) , refl , (refl , tt) , tt , mΦ)
   , mp)
   with cadr ≟ₙ sadr
... | yes _ = inj₂ (_ , n-ops ∷ n-stor ∷ [I] , _ , 0∈ ,
  ( modset cadr (refl , refl , refl , refl , refl) (wkmodβ mβ)
  , (refl , refl , wkmodΦ mΦ)
  , wkmodp mp +modp+ refl , refl))
... | no  _ = inj₂ (_ , n-ops ∷ n-stor ∷ Contract.balance sender ∸ amn ∷ [I] , _ , 0∈ ,
  ( modset cadr (refl , refl , refl , refl , refl)
   (modset sadr (refl , refl , refl , refl , refl) (wkmodβ mβ))
  , (refl , refl , refl , wkmodΦ mΦ)
  , wkmodp mp +modp+ refl , refl))

soundness {Γ} γ ασ@(αexc αccounts (inj₁ (αpr {ss = s} αself αsender αρ@(αstate αen
    (enf AMOUNT ; prg) rVM sVM Φ))) αpending)
  σ@(exc accounts (just (pr self sender ρ)) pending)
  ( mβ , (refl , refl , refl , refl , mc , ms , mρ@(refl , refl , mE , refl , mρrest))
  , mp)
  with ρ-sound γ αρ ρ mρ
... | Γ` , γ` , _ , here px , mρ` with ++-cancelʳ Γ Γ` [] (,-injectiveˡ px)
soundness γ ασ σ (mβ , ( refl , refl , refl , refl , mc , ms , mρ) , mp)
  | _ , γ` , _ , 0∈ , mρ` | refl
  = inj₂ ( _ , γ` , _ , 0∈ , (wkmodβ mβ) , (refl , refl , refl , refl
         , wkmodC {γ` = γ`} mc , (wkmodC {γ` = γ`} ms) , mρ`) , wkmodp mp)

soundness {Γ} γ ασ@(αexc αccounts (inj₁ (αpr {ss = s} αself αsender αρ@(αstate αen
    (enf BALANCE ; prg) rVM sVM Φ))) αpending)
  σ@(exc accounts (just (pr self sender ρ)) pending)
  ( mβ , (refl , refl , refl , refl , mc , ms , mρ@(refl , refl , mE , refl , mρrest))
  , mp)
  with ρ-sound γ αρ ρ mρ
... | Γ` , γ` , _ , here px , mρ` with ++-cancelʳ Γ Γ` [] (,-injectiveˡ px)
soundness γ ασ σ (mβ , ( refl , refl , refl , refl , mc , ms , mρ) , mp)
  | _ , γ` , _ , 0∈ , mρ` | refl
  = inj₂ ( _ , γ` , _ , 0∈ , (wkmodβ mβ) , (refl , refl , refl , refl
         , wkmodC {γ` = γ`} mc , (wkmodC {γ` = γ`} ms) , mρ`) , wkmodp mp)

soundness {Γ} γ ασ@(αexc αccounts (inj₁ (αpr {ss = s} αself αsender αρ@(αstate αen
    (enf (CONTRACT P) ; prg) (v∈ ∷ rVM) sVM Φ))) αpending)
  σ@(exc accounts (just (pr self sender ρ)) pending)
  ( mβ , (refl , refl , refl , refl , mc , ms , mρ@(refl , refl , mE , refl , mρrest))
  , mp)
  with ρ-sound γ αρ ρ mρ
... | Γ` , γ` , _ , here px , mρ`
  with ++-cancelʳ Γ Γ` [ option (contract P) ] (,-injectiveˡ px)
soundness γ ασ σ (mβ , ( refl , refl , refl , refl , mc , ms , mρ) , mp)
  | _ , γ` , _ , 0∈ , mρ` | refl
  = inj₂ ( _ , γ` , _ , 0∈ , (wkmodβ mβ) , (refl , refl , refl , refl
         , wkmodC {γ` = γ`} mc , (wkmodC {γ` = γ`} ms) , mρ`) , wkmodp mp)

soundness {Γ} γ ασ@(αexc αccounts (inj₁ (αpr {ss = s} αself αsender αρ@(αstate αen
    (fct (D1 {result = result} x) ; prg) rVM sVM Φ))) αpending)
  σ@(exc accounts (just (pr self sender ρ)) pending)
  ( mβ , (refl , refl , refl , refl , mc , ms , mρ@(refl , refl , mE , refl , mρrest))
  , mp)
  with ρ-sound γ αρ ρ mρ
... | Γ` , γ` , _ , here px , mρ` with ++-cancelʳ Γ Γ` [ result ] (,-injectiveˡ px)
soundness γ ασ σ (mβ , ( refl , refl , refl , refl , mc , ms , mρ) , mp)
  | _ , γ` , _ , 0∈ , mρ` | refl
  = inj₂ ( _ , γ` , _ , 0∈ , (wkmodβ mβ) , (refl , refl , refl , refl
         , wkmodC {γ` = γ`} mc , (wkmodC {γ` = γ`} ms) , mρ`) , wkmodp mp)

soundness {Γ} γ ασ@(αexc αccounts (inj₁ (αpr {ss = s} αself αsender αρ@(αstate αen
    (fct (Dm (UNPAIR {ty₁} {ty₂})) ; prg) (v∈ ∷ rVM) sVM Φ))) αpending)
  σ@(exc accounts (just (pr self sender ρ)) pending)
  ( mβ , (refl , refl , refl , refl , mc , ms , mρ@(refl , refl , mE , refl , mρrest))
  , mp)
  with ρ-sound γ αρ ρ mρ
... | Γ` , γ` , _ , here px , mρ` with ++-cancelʳ Γ Γ` [ ty₁ / ty₂ ] (,-injectiveˡ px)
soundness γ ασ σ (mβ , ( refl , refl , refl , refl , mc , ms , mρ) , mp)
  | _ , γ` , _ , 0∈ , mρ` | refl
  = inj₂ ( _ , γ` , _ , 0∈ , (wkmodβ mβ) , (refl , refl , refl , refl
         , wkmodC {γ` = γ`} mc , (wkmodC {γ` = γ`} ms) , mρ`) , wkmodp mp)

soundness {Γ} γ ασ@(αexc αccounts (inj₁ (αpr {ss = s} αself αsender αρ@(αstate αen
    (fct (Dm SWAP) ; prg) (v∈ ∷ w∈ ∷ rVM) sVM Φ))) αpending)
  σ@(exc accounts (just (pr self sender ρ)) pending)
  ( mβ , (refl , refl , refl , refl , mc , ms , mρ@(refl , refl , mE , refl , mρrest))
  , mp)
  with ρ-sound γ αρ ρ mρ
... | Γ` , γ` , _ , here px , mρ` with ++-cancelʳ Γ Γ` [] (,-injectiveˡ px)
soundness γ ασ σ (mβ , ( refl , refl , refl , refl , mc , ms , mρ) , mp)
  | _ , γ` , _ , 0∈ , mρ` | refl
  = inj₂ ( _ , γ` , _ , 0∈ , (wkmodβ mβ) , (refl , refl , refl , refl
         , wkmodC {γ` = γ`} mc , (wkmodC {γ` = γ`} ms) , mρ`) , wkmodp mp)

soundness {Γ} γ ασ@(αexc αccounts (inj₁ (αpr {ss = s} αself αsender αρ@(αstate αen
    (fct (Dm DUP) ; prg) (v∈ ∷ rVM) sVM Φ))) αpending)
  σ@(exc accounts (just (pr self sender ρ)) pending)
  ( mβ , (refl , refl , refl , refl , mc , ms , mρ@(refl , refl , mE , refl , mρrest))
  , mp)
  with ρ-sound γ αρ ρ mρ
... | Γ` , γ` , _ , here px , mρ` with ++-cancelʳ Γ Γ` [] (,-injectiveˡ px)
soundness γ ασ σ (mβ , ( refl , refl , refl , refl , mc , ms , mρ) , mp)
  | _ , γ` , _ , 0∈ , mρ` | refl
  = inj₂ ( _ , γ` , _ , 0∈ , (wkmodβ mβ) , (refl , refl , refl , refl
         , wkmodC {γ` = γ`} mc , (wkmodC {γ` = γ`} ms) , mρ`) , wkmodp mp)

soundness {Γ} γ ασ@(αexc αccounts (inj₁ (αpr {ss = s} αself αsender αρ@(αstate αen
    (fct (PUSH P x) ; prg) rVM sVM Φ))) αpending)
  σ@(exc accounts (just (pr self sender ρ)) pending)
  ( mβ , (refl , refl , refl , refl , mc , ms , mρ@(refl , refl , mE , refl , mρrest))
  , mp)
  with ρ-sound γ αρ ρ mρ
... | Γ` , γ` , _ , here px , mρ` with ++-cancelʳ Γ Γ` (expandΓ P x) (,-injectiveˡ px)
soundness γ ασ σ (mβ , ( refl , refl , refl , refl , mc , ms , mρ) , mp)
  | _ , γ` , _ , 0∈ , mρ` | refl
  = inj₂ ( _ , γ` , _ , 0∈ , (wkmodβ mβ) , (refl , refl , refl , refl
         , wkmodC {γ` = γ`} mc , (wkmodC {γ` = γ`} ms) , mρ`) , wkmodp mp)

soundness {Γ} γ ασ@(αexc αccounts (inj₁ (αpr {ss = s} αself αsender αρ@(αstate αen
    (DROP ; prg) (v∈ ∷ rVM) sVM Φ))) αpending)
  σ@(exc accounts (just (pr self sender ρ)) pending)
  ( mβ , (refl , refl , refl , refl , mc , ms , mρ@(refl , refl , mE , refl , mρrest))
  , mp)
  with ρ-sound γ αρ ρ mρ
... | Γ` , γ` , _ , here px , mρ` with ++-cancelʳ Γ Γ` [] (,-injectiveˡ px)
soundness γ ασ σ (mβ , ( refl , refl , refl , refl , mc , ms , mρ) , mp)
  | _ , γ` , _ , 0∈ , mρ` | refl
  = inj₂ ( _ , γ` , _ , 0∈ , (wkmodβ mβ) , (refl , refl , refl , refl
         , wkmodC {γ` = γ`} mc , (wkmodC {γ` = γ`} ms) , mρ`) , wkmodp mp)

soundness {Γ} γ ασ@(αexc αccounts (inj₁ (αpr {ss = s} αself αsender αρ@(αstate αen
    (ITER x ; prg) (v∈ ∷ rVM) sVM Φ))) αpending)
  σ@(exc accounts (just (pr self sender ρ)) pending)
  ( mβ , (refl , refl , refl , refl , mc , ms , mρ@(refl , refl , mE , refl , mρrest))
  , mp)
  with ρ-sound γ αρ ρ mρ
... | Γ` , γ` , _ , here px , mρ` with ++-cancelʳ Γ Γ` [] (,-injectiveˡ px)
soundness γ ασ σ (mβ , ( refl , refl , refl , refl , mc , ms , mρ) , mp)
  | _ , γ` , _ , 0∈ , mρ` | refl
  = inj₂ ( _ , γ` , _ , 0∈ , (wkmodβ mβ) , (refl , refl , refl , refl
         , wkmodC {γ` = γ`} mc , (wkmodC {γ` = γ`} ms) , mρ`) , wkmodp mp)

soundness {Γ} γ ασ@(αexc αccounts (inj₁ (αpr {ss = s} αself αsender αρ@(αstate αen
    (DIP n x ; prg) rVM sVM Φ))) αpending)
  σ@(exc accounts (just (pr self sender ρ)) pending)
  ( mβ , (refl , refl , refl , refl , mc , ms , mρ@(refl , refl , mE , refl , mρrest))
  , mp)
  with ρ-sound γ αρ ρ mρ
... | Γ` , γ` , _ , here px , mρ` with ++-cancelʳ Γ Γ` [] (,-injectiveˡ px)
soundness γ ασ σ (mβ , ( refl , refl , refl , refl , mc , ms , mρ) , mp)
  | _ , γ` , _ , 0∈ , mρ` | refl
  = inj₂ ( _ , γ` , _ , 0∈ , (wkmodβ mβ) , (refl , refl , refl , refl
         , wkmodC {γ` = γ`} mc , (wkmodC {γ` = γ`} ms) , mρ`) , wkmodp mp)

soundness {Γ} γ ασ@(αexc αccounts (inj₁ (αpr {ss = s} αself αsender αρ@(αstate αen
    (IF-NONE thn els ; prg) (v∈ ∷ rVM) sVM Φ))) αpending)
  σ@(exc accounts (just (pr self sender ρ)) pending)
  ( mβ , (refl , refl , refl , refl , mc , ms , mρ@(refl , refl , mE , refl , mρrest))
  , mp)
  with ρ-sound γ αρ ρ mρ
... | Γ` , γ` , _ , here px , mρ` with ++-cancelʳ Γ Γ` [] (,-injectiveˡ px)
soundness γ ασ σ (mβ , ( refl , refl , refl , refl , mc , ms , mρ) , mp)
  | _ , γ` , _ , 0∈ , mρ` | refl
  = inj₂ ( _ , γ` , _ , 0∈ , (wkmodβ mβ) , (refl , refl , refl , refl
         , wkmodC {γ` = γ`} mc , (wkmodC {γ` = γ`} ms) , mρ`) , wkmodp mp)
soundness {Γ} γ ασ@(αexc αccounts (inj₁ (αpr {ss = s} αself αsender αρ@(αstate αen
    (IF-NONE {t = t} thn els ; prg) (v∈ ∷ rVM) sVM Φ))) αpending)
  σ (mβ , ( refl , refl , refl , refl , mc , ms , mρ) , mp)
  | Γ` , γ` , _ , there (here px) , mρ` with ++-cancelʳ Γ Γ` [ t ] (,-injectiveˡ px)
soundness γ ασ σ (mβ , ( refl , refl , refl , refl , mc , ms , mρ) , mp)
  | _ , γ` , _ , 1∈ , mρ` | refl
  = inj₂ ( _ , γ` , _ , 1∈ , (wkmodβ mβ) , (refl , refl , refl , refl
         , wkmodC {γ` = γ`} mc , (wkmodC {γ` = γ`} ms) , mρ`) , wkmodp mp)

soundness {Γ} γ ασ@(αexc αccounts (inj₁ (αpr {ss = s} αself αsender αρ@(αstate αen
    (ITER' x ∙ prg) rVM (v∈ ∷ sVM) Φ))) αpending)
  σ@(exc accounts (just (pr self sender ρ)) pending)
  ( mβ , (refl , refl , refl , refl , mc , ms , mρ@(refl , refl , mE , refl , mρrest))
  , mp)
  with ρ-sound γ αρ ρ mρ
... | Γ` , γ` , _ , here px , mρ` with ++-cancelʳ Γ Γ` [] (,-injectiveˡ px)
soundness γ ασ σ (mβ , ( refl , refl , refl , refl , mc , ms , mρ) , mp)
  | _ , γ` , _ , 0∈ , mρ` | refl
  = inj₂ ( _ , γ` , _ , 0∈ , (wkmodβ mβ) , (refl , refl , refl , refl
         , wkmodC {γ` = γ`} mc , (wkmodC {γ` = γ`} ms) , mρ`) , wkmodp mp)
soundness {Γ} γ ασ@(αexc αccounts (inj₁ (αpr {ss = s} αself αsender αρ@(αstate αen
    (ITER' {ty} x ∙ prg) rVM (v∈ ∷ sVM) Φ))) αpending)
  σ (mβ , ( refl , refl , refl , refl , mc , ms , mρ) , mp)
  | Γ` , γ` , _ , there (here px) , mρ`
  with ++-cancelʳ Γ Γ` [ ty / list ty ] (,-injectiveˡ px)
soundness γ ασ σ (mβ , ( refl , refl , refl , refl , mc , ms , mρ) , mp)
  | _ , γ` , _ , 1∈ , mρ` | refl
  = inj₂ ( _ , γ` , _ , 1∈ , (wkmodβ mβ) , (refl , refl , refl , refl
         , wkmodC {γ` = γ`} mc , (wkmodC {γ` = γ`} ms) , mρ`) , wkmodp mp)

soundness {Γ} γ ασ@(αexc αccounts (inj₁ (αpr {ss = s} αself αsender αρ@(αstate αen
    (DIP' top ∙ prg) rVM sVM Φ))) αpending)
  σ@(exc accounts (just (pr self sender ρ)) pending)
  ( mβ , (refl , refl , refl , refl , mc , ms , mρ@(refl , refl , mE , refl , mρrest))
  , mp)
  with ρ-sound γ αρ ρ mρ
... | Γ` , γ` , _ , here px , mρ` with ++-cancelʳ Γ Γ` [] (,-injectiveˡ px)
soundness γ ασ σ (mβ , ( refl , refl , refl , refl , mc , ms , mρ) , mp)
  | _ , γ` , _ , 0∈ , mρ` | refl
  = inj₂ ( _ , γ` , _ , 0∈ , (wkmodβ mβ) , (refl , refl , refl , refl
         , wkmodC {γ` = γ`} mc , (wkmodC {γ` = γ`} ms) , mρ`) , wkmodp mp)

-----------------------------------------------------------------------------------------

