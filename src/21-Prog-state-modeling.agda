{-# OPTIONS --hidden-argument-puns #-}
module 21-Prog-state-modeling where

import 00-All-Utilities as H
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

open import Data.List.Relation.Unary.All
open import Data.List.Relation.Unary.Any
open import Data.List.Membership.Propositional using (_∈_)


------------------------- Variables, terms, Matchings -----------------------------------
-- self explanatory collection of small helper terms for modeling concrete states with
-- a context interpretation (γ : Int Γ) and a γ parameterized abstract state

val∈ : ∀ {ty Γ} → Int Γ → ty ∈ Γ → ⟦ ty ⟧
val∈ (x ∷ γ) (here refl) = x
val∈ (x ∷ γ) (there x∈)  = val∈ γ x∈

`IMI : ∀ {Γ S} → Int Γ → Match Γ S → Int S
`IMI γ [M] = [I]
`IMI γ (v∈ ∷ M) = (val∈ γ v∈) ∷ (`IMI γ M)
  
val⊢ : ∀ {ty Γ} → Int Γ → Γ ⊢ ty → ⟦ ty ⟧
val⊢ γ (const x) = x
val⊢ γ (func d1f Margs) = appD1 d1f (`IMI γ Margs)
val⊢ γ (var v∈) = val∈ γ v∈
val⊢ γ (contr {P = P} adr) = adr
val⊢ γ (m₁∈ ∸ₘ m₂∈) = val∈ γ m₁∈ ∸ val∈ γ m₂∈

-- Match models Int if all variables equal the corresponding values
-- modS stands for models Stack since Matches/Ints represent those
modS : ∀ {S Γ} → Int Γ → Match Γ S → Int S → Set
modS {S = []} γ [M] [I] = ⊤
modS {S = [ ty // S ]} γ (v∈ ∷ M) (x ∷ I) = val∈ γ v∈ ≡ x × modS γ M I

-- when a Match does model an Int, the `IMI operator will produce that Int
-- (needed for the soundness proof of symb. 1D function execution)
mod`IMI : ∀ {Γ S} {γ : Int Γ} {M : Match Γ S} {I : Int S} → modS γ M I → `IMI γ M ≡ I
mod`IMI {M = [M]} {I = []} mS = refl
mod`IMI {M = v∈ ∷ M} {I = x ∷ I} (v∈≡x , mS) = cong₂ _∷_ v∈≡x (mod`IMI mS)

-- to decompose a stack modeling into proofs that the top and bottom stacks are modeled
modS++ : ∀ {Γ γ top bot} M I → modS {top ++ bot} {Γ} γ M I
       → modS {top} γ (H.top M) (H.top I) × modS {bot} γ (H.bot M) (H.bot I)
modS++ {top = []} M I mS = tt , mS
modS++ {top = [ ty // top ]} (v∈ ∷ M) (x ∷ I) (v∈≡x , mS)
  = (v∈≡x , proj₁ (modS++ M I mS)) , (proj₂ (modS++ M I mS))

-- same as above only for the top ...
modtop : ∀ {Γ γ top bot M I}
       → modS {top ++ bot} {Γ} γ M I
       → modS {top} γ (H.top M) (H.top I)
modtop {top = []} mS = tt
modtop {top = (_ ∷ top)} {M = _ ∷ M} {_ ∷ I} (v∈≡x , mS) = v∈≡x , modtop mS

-- ... and botttom of the stack
modbot : ∀ {Γ γ top bot M I}
       → modS {top ++ bot} {Γ} γ M I
       → modS {bot} γ (H.bot M) (H.bot I)
modbot {top = []} mS  = mS
modbot {top = (_ ∷ top)} {M = [ _ ]++ M} {I = [ _ ]++ I} (_ , mS) = modbot mS


-- modbot : ∀ {Γ γ top bot Mtp Mbt I} → modS {top ++ bot} {Γ} γ (Mtp +M+ Mbt) I
--        → modS {bot} γ Mbt (Ibot I)
-- modbot {top = []}            {Mtp = [M]}                          mS  = mS
-- modbot {top = [ ty // top ]} {Mtp = v∈ ∷ Mtp} {I = x ∷ I} (v∈≡x , mS) = modbot mS

-- ... and when taking or dropping n from the stack
modtake : ∀ {Γ γ S} n M I
        → modS {S} {Γ} γ M I
        → modS {take n S} γ (H.take n M) (H.take n I)
modtake zero M I mS = tt
modtake (suc n) [M] [I] mS = tt
modtake (suc n) (v∈ ∷ M) (x ∷ I) (refl , mS) = refl , modtake n M I mS

moddrop : ∀ {Γ γ S} n M I
        → modS {S} {Γ} γ M I
        → modS {drop n S} γ (H.drop n M) (H.drop n I)
moddrop zero M I mS = mS
moddrop (suc n) [M] [I] mS = tt
moddrop (suc n) (v∈ ∷ M) (x ∷ I) (refl , mS) = moddrop n M I mS

-- two stack modelings model their concatenations
_+modS+_ : ∀ {Γ γ top Mtop Itop S `MS `IS}
         → modS {top} {Γ} γ Mtop Itop → modS {S} γ `MS `IS
         → modS γ (Mtop H.++ `MS) (Itop H.++ `IS)
_+modS+_ {top = []} {Mtop = []} {Itop = []} modtop modS = modS
_+modS+_ {top = [ ty // top ]} {v∈ ∷ Mtop} {x ∷ Itop} (refl , modtop) modS
  = refl , (modtop +modS+ modS)

------------------------- Formulas, Contracts, Blockchain -------------------------------

-- single formulas are modeled in an obvious way
modφ : ∀ {Γ} → Int Γ → Formula Γ → Set
modφ γ `false = ⊥
modφ γ (v∈ := trm) = val∈ γ v∈ ≡ val⊢ γ trm
modφ γ (x <ₘ x₁) = val∈ γ x < val∈ γ x₁
modφ γ (x ≥ₘ x₁) = val∈ γ x ≥ val∈ γ x₁

-- lists of formulas always represent their conjunction, so each formula must be modeled
modΦ : ∀ {Γ} → Int Γ → List (Formula Γ) → Set
modΦ γ [] = ⊤
modΦ γ [ φ // Φ ] = modφ γ φ × modΦ γ Φ

module alternative-mod-phi where

  modΦ′ : ∀ {Γ} → Int Γ → List (Formula Γ) → Set
  modΦ′ γ = All (modφ γ)

  modΦ⇒modΦ′ :  ∀ {Γ} → (γ : Int Γ) → (Φ : List (Formula Γ)) → modΦ γ Φ → modΦ′ γ Φ
  modΦ⇒modΦ′ γ [I] m = [I]
  modΦ⇒modΦ′ γ ([ x ]++ I) (φx , ΦI) = [ φx ]++ (modΦ⇒modΦ′ γ I ΦI)

  modΦ′⇒modΦ :  ∀ {Γ} → (γ : Int Γ) → (Φ : List (Formula Γ)) → modΦ′ γ Φ  → modΦ γ Φ
  modΦ′⇒modΦ γ [I] mΦ′ = tt
  modΦ′⇒modΦ γ ([ x ]++ Φ) ([ px ]++ mΦ′) = px , (modΦ′⇒modΦ γ Φ mΦ′)


-- abstract contracts model concrete ones in an obvious way
modC : ∀ {Γ p s} → Int Γ → αContract Γ p s → Contract p s → Set
modC γ (αctr αP αS αbalance αstorage αprogram) (ctr P S balance storage program)
  =        αP       ≡ P
  ×        αS       ≡ S
  × val∈ γ αbalance ≡ balance
  × val∈ γ αstorage ≡ storage
  ×        αprogram ≡ program

-- subterm for modeling blockchains, models when types match and the contract is modeled
modMC : ∀ {Γ} → Int Γ → Maybe (∃[ αp ] ∃[ αs ] αContract Γ αp αs)
                      → Maybe (∃[  p ] ∃[  s ]  Contract    p  s) → Set
modMC γ (just (αp , αs , αc)) (just (p , s , c))
  = Σ (αp ≡ p) λ{ refl → Σ (αs ≡ s) λ{ refl → modC γ αc c } }
modMC γ nothing nothing = ⊤
modMC γ _ _ = ⊥

-- ... don't now much else to say than Agda magic :D
-- ... yeah, sorry, can't explain it, but it makes sense, think about it ;)
modβ : ∀ {Γ} → Int Γ → βlockchain Γ → Blockchain → Set
modβ γ βl bl = ∀ a → modMC γ (βl a) (bl a)

------------------------- Environments and ⊎Program-states ------------------------------

-- environment modeling ... obvious
modE : ∀ {Γ} → Int Γ → αEnvironment Γ → Environment → Set
modE γ (αenv αccounts αself αsender αbalance αamount)
        (env accounts  self  sender  balance  amount)
  = modβ γ αccounts accounts
  ×        αself ≡ self
  ×        αsender  ≡ sender
  × val∈ γ αbalance ≡ balance
  × val∈ γ αamount  ≡ amount
        
-- to model a program state, the output stacks will match implicitly by applying this
-- operator, but equality of the input stacks must be given explicitly
-- the rest is equality of the given programs and modelings of every subcomponent
modρ : ∀ {Γ} → Int Γ → αProg-state Γ ro so → Prog-state ro so → Set
modρ γ (αstate {ri = αri} {si = αsi} αen αprg rVM sVM Φ) (state {ri} {si} en prg stk s`SI)
  = Σ (αri ≡ ri) λ{ refl → Σ (αsi ≡ si) λ{ refl
    → modE γ αen en × αprg ≡ prg × modS γ rVM stk × modS γ sVM s`SI × modΦ γ Φ} }

-- a disjunction of program states is modeled if one of them is modeled
-- different approaches are possible but this one is most concise and efficient
mod⊎ρ : ∀ {Γ} → Int Γ → ⊎Prog-state ro so → Prog-state ro so → Set
mod⊎ρ {Γ} γ ⊎ρ ρ = ∃[ αρ ] (Γ , αρ) ∈ ⊎ρ × modρ γ αρ ρ

