
module 25-2-exec-step-soundness where

open import 01-Types
open import 02-Functions-Interpretations
open import 03-2-concrete-execution
open import 11-abstract-representation-and-weakening
open import 12-2-abstract-execution-accessories-and-weakening
open import 13-2-abstract-Prog-state-execution
open import 14-2-abstract-Exec-state-execution
open import 21-2-Prog-state-modeling
open import 22-2-P-s-m-weakening
open import 23-2-prog-step-soundness renaming (soundness to ρ-sound)
open import 24-2-Exec-state-modeling

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

soundness : ∀ {Γ} (γ : Int Γ) → ∀ ασ σ → modσ γ ασ σ
          → ExecState.MPstate σ ≡ inj₂ tt
          ⊎ ∃[ Γ` ] ∃[ γ` ] mod⊎σ {Γ` ++ Γ} (γ` +I+ γ) (αexec-step ασ) (exec-step σ)

soundness γ (exc αccounts (inj₂ Φ)  αpending)
            (exc accounts (inj₂ tt) pending) mσ = inj₁ refl

soundness γ
  (exc αccounts
        (inj₁ (pr {ss = s} αself αsender (state
          (env _  cadr  sadr blc∈ amn∈) end (no,ns∈ ∷ [M]) [M] Φ)))
        αpending)
   (exc accounts
        (inj₁ (pr self sender (state
           (env _ .cadr .sadr blc  amn) .end ((n-ops , n-stor) ∷ [I]) [I] tt)))
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

soundness {Γ} γ ασ@(exc αccounts (inj₁ (pr {ss = s} αself αsender αρ@(state αen
    (enf AMOUNT ; prg) rVM sVM Φ))) αpending)
  σ@(exc accounts (inj₁ (pr self sender ρ)) pending)
  ( mβ , (refl , refl , refl , refl , mc , ms , mρ@(refl , refl , mE , refl , mρrest))
  , mp)
  with ρ-sound γ αρ ρ mρ
... | Γ` , γ` , _ , here px , mρ` with ++-cancelʳ Γ Γ` [] (,-injectiveˡ px)
soundness γ ασ σ (mβ , ( refl , refl , refl , refl , mc , ms , mρ) , mp)
  | _ , γ` , _ , 0∈ , mρ` | refl
  = inj₂ ( _ , γ` , _ , 0∈ , (wkmodβ mβ) , (refl , refl , refl , refl
         , wkmodC {γ` = γ`} mc , (wkmodC {γ` = γ`} ms) , mρ`) , wkmodp mp)

soundness {Γ} γ ασ@(exc αccounts (inj₁ (pr {ss = s} αself αsender αρ@(state αen
    (enf BALANCE ; prg) rVM sVM Φ))) αpending)
  σ@(exc accounts (inj₁ (pr self sender ρ)) pending)
  ( mβ , (refl , refl , refl , refl , mc , ms , mρ@(refl , refl , mE , refl , mρrest))
  , mp)
  with ρ-sound γ αρ ρ mρ
... | Γ` , γ` , _ , here px , mρ` with ++-cancelʳ Γ Γ` [] (,-injectiveˡ px)
soundness γ ασ σ (mβ , ( refl , refl , refl , refl , mc , ms , mρ) , mp)
  | _ , γ` , _ , 0∈ , mρ` | refl
  = inj₂ ( _ , γ` , _ , 0∈ , (wkmodβ mβ) , (refl , refl , refl , refl
         , wkmodC {γ` = γ`} mc , (wkmodC {γ` = γ`} ms) , mρ`) , wkmodp mp)

soundness {Γ} γ ασ@(exc αccounts (inj₁ (pr {ss = s} αself αsender αρ@(state αen
    (enf (CONTRACT P) ; prg) (v∈ ∷ rVM) sVM Φ))) αpending)
  σ@(exc accounts (inj₁ (pr self sender ρ)) pending)
  ( mβ , (refl , refl , refl , refl , mc , ms , mρ@(refl , refl , mE , refl , mρrest))
  , mp)
  with ρ-sound γ αρ ρ mρ
... | Γ` , γ` , _ , here px , mρ`
  with ++-cancelʳ Γ Γ` [ option (contract P) ] (,-injectiveˡ px)
soundness γ ασ σ (mβ , ( refl , refl , refl , refl , mc , ms , mρ) , mp)
  | _ , γ` , _ , 0∈ , mρ` | refl
  = inj₂ ( _ , γ` , _ , 0∈ , (wkmodβ mβ) , (refl , refl , refl , refl
         , wkmodC {γ` = γ`} mc , (wkmodC {γ` = γ`} ms) , mρ`) , wkmodp mp)

soundness {Γ} γ ασ@(exc αccounts (inj₁ (pr {ss = s} αself αsender αρ@(state αen
    (fct (D1 {result = result} x) ; prg) rVM sVM Φ))) αpending)
  σ@(exc accounts (inj₁ (pr self sender ρ)) pending)
  ( mβ , (refl , refl , refl , refl , mc , ms , mρ@(refl , refl , mE , refl , mρrest))
  , mp)
  with ρ-sound γ αρ ρ mρ
... | Γ` , γ` , _ , here px , mρ` with ++-cancelʳ Γ Γ` [ result ] (,-injectiveˡ px)
soundness γ ασ σ (mβ , ( refl , refl , refl , refl , mc , ms , mρ) , mp)
  | _ , γ` , _ , 0∈ , mρ` | refl
  = inj₂ ( _ , γ` , _ , 0∈ , (wkmodβ mβ) , (refl , refl , refl , refl
         , wkmodC {γ` = γ`} mc , (wkmodC {γ` = γ`} ms) , mρ`) , wkmodp mp)

soundness {Γ} γ ασ@(exc αccounts (inj₁ (pr {ss = s} αself αsender αρ@(state αen
    (fct (Dm (UNPAIR {ty₁} {ty₂})) ; prg) (v∈ ∷ rVM) sVM Φ))) αpending)
  σ@(exc accounts (inj₁ (pr self sender ρ)) pending)
  ( mβ , (refl , refl , refl , refl , mc , ms , mρ@(refl , refl , mE , refl , mρrest))
  , mp)
  with ρ-sound γ αρ ρ mρ
... | Γ` , γ` , _ , here px , mρ` with ++-cancelʳ Γ Γ` [ ty₁ / ty₂ ] (,-injectiveˡ px)
soundness γ ασ σ (mβ , ( refl , refl , refl , refl , mc , ms , mρ) , mp)
  | _ , γ` , _ , 0∈ , mρ` | refl
  = inj₂ ( _ , γ` , _ , 0∈ , (wkmodβ mβ) , (refl , refl , refl , refl
         , wkmodC {γ` = γ`} mc , (wkmodC {γ` = γ`} ms) , mρ`) , wkmodp mp)

soundness {Γ} γ ασ@(exc αccounts (inj₁ (pr {ss = s} αself αsender αρ@(state αen
    (fct (Dm SWAP) ; prg) (v∈ ∷ w∈ ∷ rVM) sVM Φ))) αpending)
  σ@(exc accounts (inj₁ (pr self sender ρ)) pending)
  ( mβ , (refl , refl , refl , refl , mc , ms , mρ@(refl , refl , mE , refl , mρrest))
  , mp)
  with ρ-sound γ αρ ρ mρ
... | Γ` , γ` , _ , here px , mρ` with ++-cancelʳ Γ Γ` [] (,-injectiveˡ px)
soundness γ ασ σ (mβ , ( refl , refl , refl , refl , mc , ms , mρ) , mp)
  | _ , γ` , _ , 0∈ , mρ` | refl
  = inj₂ ( _ , γ` , _ , 0∈ , (wkmodβ mβ) , (refl , refl , refl , refl
         , wkmodC {γ` = γ`} mc , (wkmodC {γ` = γ`} ms) , mρ`) , wkmodp mp)

soundness {Γ} γ ασ@(exc αccounts (inj₁ (pr {ss = s} αself αsender αρ@(state αen
    (fct (Dm DUP) ; prg) (v∈ ∷ rVM) sVM Φ))) αpending)
  σ@(exc accounts (inj₁ (pr self sender ρ)) pending)
  ( mβ , (refl , refl , refl , refl , mc , ms , mρ@(refl , refl , mE , refl , mρrest))
  , mp)
  with ρ-sound γ αρ ρ mρ
... | Γ` , γ` , _ , here px , mρ` with ++-cancelʳ Γ Γ` [] (,-injectiveˡ px)
soundness γ ασ σ (mβ , ( refl , refl , refl , refl , mc , ms , mρ) , mp)
  | _ , γ` , _ , 0∈ , mρ` | refl
  = inj₂ ( _ , γ` , _ , 0∈ , (wkmodβ mβ) , (refl , refl , refl , refl
         , wkmodC {γ` = γ`} mc , (wkmodC {γ` = γ`} ms) , mρ`) , wkmodp mp)

soundness {Γ} γ ασ@(exc αccounts (inj₁ (pr {ss = s} αself αsender αρ@(state αen
    (fct (PUSH P x) ; prg) rVM sVM Φ))) αpending)
  σ@(exc accounts (inj₁ (pr self sender ρ)) pending)
  ( mβ , (refl , refl , refl , refl , mc , ms , mρ@(refl , refl , mE , refl , mρrest))
  , mp)
  with ρ-sound γ αρ ρ mρ
... | Γ` , γ` , _ , here px , mρ` with ++-cancelʳ Γ Γ` (expandΓ P x) (,-injectiveˡ px)
soundness γ ασ σ (mβ , ( refl , refl , refl , refl , mc , ms , mρ) , mp)
  | _ , γ` , _ , 0∈ , mρ` | refl
  = inj₂ ( _ , γ` , _ , 0∈ , (wkmodβ mβ) , (refl , refl , refl , refl
         , wkmodC {γ` = γ`} mc , (wkmodC {γ` = γ`} ms) , mρ`) , wkmodp mp)

soundness {Γ} γ ασ@(exc αccounts (inj₁ (pr {ss = s} αself αsender αρ@(state αen
    (DROP ; prg) (v∈ ∷ rVM) sVM Φ))) αpending)
  σ@(exc accounts (inj₁ (pr self sender ρ)) pending)
  ( mβ , (refl , refl , refl , refl , mc , ms , mρ@(refl , refl , mE , refl , mρrest))
  , mp)
  with ρ-sound γ αρ ρ mρ
... | Γ` , γ` , _ , here px , mρ` with ++-cancelʳ Γ Γ` [] (,-injectiveˡ px)
soundness γ ασ σ (mβ , ( refl , refl , refl , refl , mc , ms , mρ) , mp)
  | _ , γ` , _ , 0∈ , mρ` | refl
  = inj₂ ( _ , γ` , _ , 0∈ , (wkmodβ mβ) , (refl , refl , refl , refl
         , wkmodC {γ` = γ`} mc , (wkmodC {γ` = γ`} ms) , mρ`) , wkmodp mp)

soundness {Γ} γ ασ@(exc αccounts (inj₁ (pr {ss = s} αself αsender αρ@(state αen
    (ITER x ; prg) (v∈ ∷ rVM) sVM Φ))) αpending)
  σ@(exc accounts (inj₁ (pr self sender ρ)) pending)
  ( mβ , (refl , refl , refl , refl , mc , ms , mρ@(refl , refl , mE , refl , mρrest))
  , mp)
  with ρ-sound γ αρ ρ mρ
... | Γ` , γ` , _ , here px , mρ` with ++-cancelʳ Γ Γ` [] (,-injectiveˡ px)
soundness γ ασ σ (mβ , ( refl , refl , refl , refl , mc , ms , mρ) , mp)
  | _ , γ` , _ , 0∈ , mρ` | refl
  = inj₂ ( _ , γ` , _ , 0∈ , (wkmodβ mβ) , (refl , refl , refl , refl
         , wkmodC {γ` = γ`} mc , (wkmodC {γ` = γ`} ms) , mρ`) , wkmodp mp)

soundness {Γ} γ ασ@(exc αccounts (inj₁ (pr {ss = s} αself αsender αρ@(state αen
    (DIP n x ; prg) rVM sVM Φ))) αpending)
  σ@(exc accounts (inj₁ (pr self sender ρ)) pending)
  ( mβ , (refl , refl , refl , refl , mc , ms , mρ@(refl , refl , mE , refl , mρrest))
  , mp)
  with ρ-sound γ αρ ρ mρ
... | Γ` , γ` , _ , here px , mρ` with ++-cancelʳ Γ Γ` [] (,-injectiveˡ px)
soundness γ ασ σ (mβ , ( refl , refl , refl , refl , mc , ms , mρ) , mp)
  | _ , γ` , _ , 0∈ , mρ` | refl
  = inj₂ ( _ , γ` , _ , 0∈ , (wkmodβ mβ) , (refl , refl , refl , refl
         , wkmodC {γ` = γ`} mc , (wkmodC {γ` = γ`} ms) , mρ`) , wkmodp mp)

soundness {Γ} γ ασ@(exc αccounts (inj₁ (pr {ss = s} αself αsender αρ@(state αen
    (IF-NONE thn els ; prg) (v∈ ∷ rVM) sVM Φ))) αpending)
  σ@(exc accounts (inj₁ (pr self sender ρ)) pending)
  ( mβ , (refl , refl , refl , refl , mc , ms , mρ@(refl , refl , mE , refl , mρrest))
  , mp)
  with ρ-sound γ αρ ρ mρ
... | Γ` , γ` , _ , here px , mρ` with ++-cancelʳ Γ Γ` [] (,-injectiveˡ px)
soundness γ ασ σ (mβ , ( refl , refl , refl , refl , mc , ms , mρ) , mp)
  | _ , γ` , _ , 0∈ , mρ` | refl
  = inj₂ ( _ , γ` , _ , 0∈ , (wkmodβ mβ) , (refl , refl , refl , refl
         , wkmodC {γ` = γ`} mc , (wkmodC {γ` = γ`} ms) , mρ`) , wkmodp mp)
soundness {Γ} γ ασ@(exc αccounts (inj₁ (pr {ss = s} αself αsender αρ@(state αen
    (IF-NONE {t = t} thn els ; prg) (v∈ ∷ rVM) sVM Φ))) αpending)
  σ (mβ , ( refl , refl , refl , refl , mc , ms , mρ) , mp)
  | Γ` , γ` , _ , there (here px) , mρ` with ++-cancelʳ Γ Γ` [ t ] (,-injectiveˡ px)
soundness γ ασ σ (mβ , ( refl , refl , refl , refl , mc , ms , mρ) , mp)
  | _ , γ` , _ , 1∈ , mρ` | refl
  = inj₂ ( _ , γ` , _ , 1∈ , (wkmodβ mβ) , (refl , refl , refl , refl
         , wkmodC {γ` = γ`} mc , (wkmodC {γ` = γ`} ms) , mρ`) , wkmodp mp)

soundness {Γ} γ ασ@(exc αccounts (inj₁ (pr {ss = s} αself αsender αρ@(state αen
    (ITER' x ∙ prg) rVM (v∈ ∷ sVM) Φ))) αpending)
  σ@(exc accounts (inj₁ (pr self sender ρ)) pending)
  ( mβ , (refl , refl , refl , refl , mc , ms , mρ@(refl , refl , mE , refl , mρrest))
  , mp)
  with ρ-sound γ αρ ρ mρ
... | Γ` , γ` , _ , here px , mρ` with ++-cancelʳ Γ Γ` [] (,-injectiveˡ px)
soundness γ ασ σ (mβ , ( refl , refl , refl , refl , mc , ms , mρ) , mp)
  | _ , γ` , _ , 0∈ , mρ` | refl
  = inj₂ ( _ , γ` , _ , 0∈ , (wkmodβ mβ) , (refl , refl , refl , refl
         , wkmodC {γ` = γ`} mc , (wkmodC {γ` = γ`} ms) , mρ`) , wkmodp mp)
soundness {Γ} γ ασ@(exc αccounts (inj₁ (pr {ss = s} αself αsender αρ@(state αen
    (ITER' {ty} x ∙ prg) rVM (v∈ ∷ sVM) Φ))) αpending)
  σ (mβ , ( refl , refl , refl , refl , mc , ms , mρ) , mp)
  | Γ` , γ` , _ , there (here px) , mρ`
  with ++-cancelʳ Γ Γ` [ ty / list ty ] (,-injectiveˡ px)
soundness γ ασ σ (mβ , ( refl , refl , refl , refl , mc , ms , mρ) , mp)
  | _ , γ` , _ , 1∈ , mρ` | refl
  = inj₂ ( _ , γ` , _ , 1∈ , (wkmodβ mβ) , (refl , refl , refl , refl
         , wkmodC {γ` = γ`} mc , (wkmodC {γ` = γ`} ms) , mρ`) , wkmodp mp)

soundness {Γ} γ ασ@(exc αccounts (inj₁ (pr {ss = s} αself αsender αρ@(state αen
    (DIP' top ∙ prg) rVM sVM Φ))) αpending)
  σ@(exc accounts (inj₁ (pr self sender ρ)) pending)
  ( mβ , (refl , refl , refl , refl , mc , ms , mρ@(refl , refl , mE , refl , mρrest))
  , mp)
  with ρ-sound γ αρ ρ mρ
... | Γ` , γ` , _ , here px , mρ` with ++-cancelʳ Γ Γ` [] (,-injectiveˡ px)
soundness γ ασ σ (mβ , ( refl , refl , refl , refl , mc , ms , mρ) , mp)
  | _ , γ` , _ , 0∈ , mρ` | refl
  = inj₂ ( _ , γ` , _ , 0∈ , (wkmodβ mβ) , (refl , refl , refl , refl
         , wkmodC {γ` = γ`} mc , (wkmodC {γ` = γ`} ms) , mρ`) , wkmodp mp)

-----------------------------------------------------------------------------------------

