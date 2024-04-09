
module 24-2-Exec-state-modeling where

open import 01-Types
open import 02-Functions-Interpretations
open import 03-2-concrete-execution
open import 11-abstract-representation-and-weakening
open import 12-2-abstract-execution-accessories-and-weakening
open import 13-2-abstract-Prog-state-execution
open import 21-2-Prog-state-modeling
open import 22-2-P-s-m-weakening

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

-- modr : ∀ {Γ} → Int Γ → αPrgRunning Γ ⊎ List (Formula Γ) → CPrgRunning ⊎ ⊤ → Set

modr : ∀ {Γ} → Int Γ → MODELING Γ RunMode
modr γ (Run (pr {αp} {αs} {αx} {αy} αself αsender αρ))
       (Run (pr  {p}  {s}  {x}  {y}  self  sender  ρ))
  = Σ (αp ≡ p) λ{ refl → Σ (αs ≡ s) λ{ refl → Σ (αx ≡ x) λ{ refl → Σ (αy ≡ y) λ{ refl
    → modC γ αself self × modC γ αsender sender × modρ γ αρ ρ } } } }
modr γ (Cont Φ) (Cont tt) = modΦ γ Φ
modr γ (`AFail Φ) (Fail tt) = modΦ γ Φ
modr γ (`APanic Φ) (`INJ₂ tt) = modΦ γ Φ
modr γ αr r = ⊥

modt : ∀ {Γ} → Int Γ → MODELING Γ Transaction
modt γ (pops , psender) (pops₁ , psender₁) = val∈ γ pops ≡ pops₁ × psender ≡ psender₁

-- modp : ∀ {Γ} → Int Γ → List (αTransaction Γ)
--                      → List (CTransaction) → Set

modp : ∀ {Γ} → Int Γ → MODELING Γ λ M → List (Transaction M)
modp γ [] [] = ⊤
modp γ [ lops∈ , sadr // αp ] [ lops , sadr₁ // p ]
  = val∈ γ lops∈ ≡ lops × sadr ≡ sadr₁ × modp γ αp p
modp γ αp p = ⊥
        
modσ : ∀ {Γ} → Int Γ → MODELING Γ ExecState
modσ γ (exc αccounts αρ⊎Φ αpending) (exc accounts MPstate pending)
  with αρ⊎Φ
... | `APanic Φ = ⊤
... | _ 
  = modβ γ αccounts accounts
  × modr γ αρ⊎Φ MPstate
  × modp γ αpending pending
pattern modσ⟨_,_,_⟩ a b c = a , b , c

-- modσ-injective : ∀ {Γ} → (γ : Int Γ) → ∀ {αccounts αρ⊎Φ αpending accounts MPstate pending} →
--   {mb₁ mb₂ : modβ γ αccounts accounts}
--   {mr₁ mr₂ : modr γ αρ⊎Φ MPstate}
--   {mp₁ mp₂ : modp γ αpending pending}
--   → _≡_ {A = modσ γ (exc αccounts αρ⊎Φ αpending) (exc accounts MPstate pending)} modσ⟨ mb₁ , mr₁ , mp₁ ⟩ modσ⟨ mb₂ , mr₂ , mp₂ ⟩
--   → Σ (mb₁ ≡ mb₂) λ {refl → Σ (mr₁ ≡ mr₂) λ {refl → mp₁ ≡ mp₂}}
-- modσ-injective γ ms≡ = {!!}

mod⊎σ : ∀ {Γ} → Int Γ → ⊎ExecState → CExecState → Set
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

