
module 21-Prog-state-modeling where

open import 01-Types
open import 02-Functions-Interpretations
open import 03-concrete-execution
open import 11-abstract-representation-and-weakening
open import 12-abstract-execution-accessories-and-weakening

open import Relation.Binary.PropositionalEquality.Core

open import Data.Nat
open import Data.List.Base hiding ([_]; unfold)
open import Data.Maybe.Base
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Data.Empty

open import Data.List.Relation.Unary.Any
open import Data.List.Membership.Propositional using (_∈_)


------------------------- Variables, terms, Matchings -----------------------------------

val∈ : ∀ {ty Γ} → Int Γ → ty ∈ Γ → ⟦ ty ⟧
val∈ (x ∷ I) (here refl) = x
val∈ (x ∷ I) (there x∈)  = val∈ I x∈

IMI : ∀ {Γ S} → Int Γ → Match Γ S → Int S
IMI γ [M] = [I]
IMI γ (v∈ ∷ M) = (val∈ γ v∈) ∷ (IMI γ M)
  
val⊢ : ∀ {ty Γ} → Int Γ → Γ ⊢ ty → ⟦ ty ⟧
val⊢ γ (const x) = x
val⊢ γ (func d1f Margs) = appD1 d1f (IMI γ Margs)
val⊢ γ (var v∈) = val∈ γ v∈
val⊢ γ (contr {P = P} adr) = adr
val⊢ γ (m₁∈ ∸ₘ m₂∈) = val∈ γ m₁∈ ∸ val∈ γ m₂∈

modS : ∀ {S Γ} → Int Γ → Match Γ S → Int S → Set
modS {[]} γ [M] [I] = ⊤
modS {[ ty // S ]} γ (v∈ ∷ M) (x ∷ I) = val∈ γ v∈ ≡ x × modS γ M I

modIMI : ∀ {Γ S} {γ : Int Γ} {M : Match Γ S} {I : Int S} → modS γ M I → IMI γ M ≡ I
modIMI {M = [M]} {[I]} mS = refl
modIMI {M = v∈ ∷ M} {x ∷ I} (v∈≡x , mS) = cong₂ _∷_ v∈≡x (modIMI mS)

modS++ : ∀ {Γ γ top bot} M I → modS {top ++ bot} {Γ} γ M I
       → modS {top} γ (Mtop M) (Itop I) × modS {bot} γ (Mbot M) (Ibot I)
modS++ {top = []} M I mS = tt , mS
modS++ {top = [ ty // top ]} (v∈ ∷ M) (x ∷ I) (v∈≡x , mS)
  = (v∈≡x , proj₁ (modS++ M I mS)) , (proj₂ (modS++ M I mS))

modtop : ∀ {Γ γ top bot M I} → modS {top ++ bot} {Γ} γ M I
       → modS {top} γ (Mtop M) (Itop I)
modtop {top = []} mS = tt
modtop {top = [ ty // top ]} {M = v∈ ∷ M} {x ∷ I} (v∈≡x , mS) = v∈≡x , modtop mS

-- modbot : ∀ {Γ γ top bot M I} → modS {top ++ bot} {Γ} γ M I
       -- → modS {bot} γ (Mbot M) (Ibot I)
-- modbot {top = []} mS = mS
-- modbot {top = [ ty // top ]} {M = v∈ ∷ M} {x ∷ I} (v∈≡x , mS) = modbot mS

modbot : ∀ {Γ γ top bot Mtp Mbt I} → modS {top ++ bot} {Γ} γ (Mtp +M+ Mbt) I
       → modS {bot} γ Mbt (Ibot I)
modbot {top = []}            {Mtp = [M]}                          mS  = mS
modbot {top = [ ty // top ]} {Mtp = v∈ ∷ Mtp} {I = x ∷ I} (v∈≡x , mS) = modbot mS

modtake : ∀ {Γ γ S} n M I → modS {S} {Γ} γ M I
        → modS {take n S} γ (takeM n M) (takeI n I)
modtake zero M I mS = tt
modtake (suc n) [M] [I] mS = tt
modtake (suc n) (v∈ ∷ M) (x ∷ I) (refl , mS) = refl , modtake n M I mS

moddrop : ∀ {Γ γ S} n M I → modS {S} {Γ} γ M I
        → modS {drop n S} γ (dropM n M) (dropI n I)
moddrop zero M I mS = mS
moddrop (suc n) [M] [I] mS = tt
moddrop (suc n) (v∈ ∷ M) (x ∷ I) (refl , mS) = moddrop n M I mS

_+modS+_ : ∀ {Γ γ top Mtop Itop S MS IS}
         → modS {top} {Γ} γ Mtop Itop → modS {S} γ MS IS
         → modS γ (Mtop +M+ MS) (Itop +I+ IS)
_+modS+_ {top = []} {[M]} {[I]} modtop modS = modS
_+modS+_ {top = [ ty // top ]} {v∈ ∷ Mtop} {x ∷ Itop} (refl , modtop) modS
  = refl , (modtop +modS+ modS)

------------------------- Formulas, Contracts, Blockchain -------------------------------

modφ : ∀ {Γ} → Int Γ → Formula Γ → Set
modφ γ `false = ⊥
modφ γ (v∈ := trm) = val∈ γ v∈ ≡ val⊢ γ trm
modφ γ (x <ₘ x₁) = val∈ γ x < val∈ γ x₁
modφ γ (x ≥ₘ x₁) = val∈ γ x ≥ val∈ γ x₁

modΦ : ∀ {Γ} → Int Γ → List (Formula Γ) → Set
modΦ γ [] = ⊤
modΦ γ [ φ // Φ ] = modφ γ φ × modΦ γ Φ

modC : ∀ {Γ p s} → Int Γ → αContract Γ {p} {s} → Contract {p} {s} → Set
modC γ (αctr αP αS αbalance αstorage αprogram) (ctr P S balance storage program)
  =        αP       ≡ P
  ×        αS       ≡ S
  × val∈ γ αbalance ≡ balance
  × val∈ γ αstorage ≡ storage
  ×        αprogram ≡ program

modMC : ∀ {Γ} → Int Γ → Maybe (∃[ αp ] ∃[ αs ] αContract Γ {αp} {αs})
                      → Maybe (∃[  p ] ∃[  s ]  Contract    {p}  {s}) → Set
modMC γ (just (αp , αs , αc)) (just (p , s , c))
  = Σ (αp ≡ p) λ{ refl → Σ (αs ≡ s) λ{ refl → modC γ αc c } }
modMC γ nothing nothing = ⊤
modMC γ _ _ = ⊥

modβ : ∀ {Γ} → Int Γ → βlockchain Γ → Blockchain → Set
modβ γ βl bl = ∀ a → modMC γ (βl a) (bl a)

------------------------- Environments and ⊎Program-states ------------------------------

modE : ∀ {Γ} → Int Γ → αEnvironment Γ → Environment → Set
modE γ (αenv αccounts αcurrent αsender αbalance αamount)
        (env accounts  current  sender  balance  amount)
  = modβ γ αccounts accounts
  ×        αcurrent ≡ current
  ×        αsender  ≡ sender
  × val∈ γ αbalance ≡ balance
  × val∈ γ αamount  ≡ amount
        
modρ : ∀ {Γ ro so} → Int Γ → αProg-state Γ {ro} {so} → Prog-state {ro} {so} → Set
modρ γ (αstate {αri} {αsi} αen αprg rVM sVM Φ) (state {ri} {si} en prg rSI sSI)
  = Σ (αri ≡ ri) λ{ refl → Σ (αsi ≡ si) λ{ refl
    → modE γ αen en × αprg ≡ prg × modS γ rVM rSI × modS γ sVM sSI × modΦ γ Φ} }

mod⊎ρ : ∀ {Γ ro so} → Int Γ → ⊎Prog-state {ro} {so} → Prog-state {ro} {so} → Set
mod⊎ρ {Γ} γ ⊎ρ ρ = ∃[ αρ ] (Γ , αρ) ∈ ⊎ρ × modρ γ αρ ρ

