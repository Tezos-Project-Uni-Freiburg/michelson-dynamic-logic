
module 24-Exec-state-modeling where

open import 01-Types
open import 02-Functions-Interpretations
open import 03-concrete-execution
open import 11-abstract-representation-and-weakening
open import 12-abstract-execution-accessories-and-weakening
open import 13-abstract-Prog-state-execution
open import 21-Prog-state-modeling
open import 22-P-s-m-weakening

open import Relation.Binary.PropositionalEquality.Core
open import Relation.Nullary

open import Data.Nat renaming (_≟_ to _≟ₙ_) hiding (_/_)
open import Data.List.Base hiding ([_]; unfold)
open import Data.Maybe.Base
open import Data.Product
open import Data.Sum hiding ([_,_])
open import Data.Unit
open import Data.Empty

open import Data.List.Relation.Unary.Any
open import Data.List.Membership.Propositional using (_∈_)


------------------------- Variables, terms, Matchings -----------------------------------

modr : ∀ {Γ} → Int Γ → αPrg-running Γ ⊎ List (Formula Γ) → Maybe Prg-running → Set
modr γ (inj₁ (αpr {αp} {αs} {αx} {αy} αcurrent αsender αρ))
       (just  (pr  {p}  {s}  {x}  {y}  current  sender  ρ))
  = Σ (αp ≡ p) λ{ refl → Σ (αs ≡ s) λ{ refl → Σ (αx ≡ x) λ{ refl → Σ (αy ≡ y) λ{ refl
    → modC γ αcurrent current × modC γ αsender sender × modρ γ αρ ρ } } } }
modr γ (inj₂ Φ) nothing = modΦ γ Φ
modr γ αr r = ⊥

modp : ∀ {Γ} → Int Γ → List (αPending Γ)
                     → List (Pending) → Set
modp γ [] [] = ⊤
modp γ [ lops∈ , sadr // αp ] [ lops , sadr₁ // p ]
  = val∈ γ lops∈ ≡ lops × sadr ≡ sadr₁ × modp γ αp p
modp γ αp p = ⊥
        
modσ : ∀ {Γ} → Int Γ → αExec-state Γ → Exec-state → Set
modσ γ (αexc αccounts αρ⊎Φ αpending) (exc accounts MPstate pending)
  = modβ γ αccounts accounts × modr γ αρ⊎Φ MPstate × modp γ αpending pending

mod⊎σ : ∀ {Γ} → Int Γ → ⊎Exec-state → Exec-state → Set
mod⊎σ {Γ} γ ⊎σ σ = ∃[ ασ ] (Γ , ασ) ∈ ⊎σ × modσ γ ασ σ

_+modp+_,_ : ∀ {Γ γ αp p lops∈ lops adr}
         → modp {Γ} γ αp p → val∈ γ lops∈ ≡ lops → adr ≡ adr
         → modp γ (αp ++ [ lops∈ , adr ]) (p ++ [ lops , adr ])
_+modp+_,_ {αp = []} {[]} tt lops≡ refl = lops≡ , refl , tt
_+modp+_,_ {αp = [ αol // αp ]} {[ ol // p ]} (refl , refl , mp) lops≡ refl
  = refl , refl , mp +modp+ lops≡ , refl

wkmodp : ∀ {Γ` Γ γ γ` αp p} → modp {Γ} γ αp p → modp {Γ` ++ Γ} (γ` +I+ γ) (wkp αp) p
wkmodp {αp = []} {[]} mp = tt
wkmodp {γ` = γ`} {[ x // αp ]} {[ x₁ // p ]} (refl , refl , mp)
  = wkval∈ {γ` = γ`} , refl , (wkmodp mp)

modset : ∀ {Γ γ βl bl p s αc c} adr → modC {Γ} {p} {s} γ αc c → modβ {Γ} γ βl bl
        → modβ γ (βset adr αc βl) (set adr c bl)
modset adr mC mβ a with a ≟ₙ adr
... | yes refl = refl , refl , mC
... | no  _    = mβ a

