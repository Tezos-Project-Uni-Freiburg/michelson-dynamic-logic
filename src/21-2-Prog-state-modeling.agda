{-# OPTIONS --hidden-argument-puns #-}
module 21-2-Prog-state-modeling where

import 00-All-Utilities as H
open import 01-Types
open import 02-Functions-Interpretations
open import 03-2-concrete-execution
open import 11-abstract-representation-and-weakening
open import 12-2-abstract-execution-accessories-and-weakening

open import Relation.Binary.PropositionalEquality.Core

open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _<_; _≥_)
open import Data.List.Base hiding ([_]; unfold; lookup; map)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃-syntax; Σ)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit
open import Data.Empty

open import Data.List.Relation.Unary.All using (All; [] ; _∷_; lookup ; map)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Membership.Propositional using (_∈_)


------------------------- Variables, terms, Matchings -----------------------------------
-- self explanatory collection of small helper terms for modeling concrete states with
-- a context interpretation (γ : Int Γ) and a γ parameterized abstract state

val∈ : ∀ {Γ} → Int Γ → ∀ {ty} → ty ∈ Γ → ⟦ ty ⟧
val∈ = lookup

`IMI : ∀ {Γ S} → Int Γ → Match Γ S → Int S
`IMI γ = map (val∈ γ)
  
val⊢ : ∀ {ty Γ} → Int Γ → Γ ⊢ ty → ⟦ ty ⟧
val⊢ γ (const x) = x
val⊢ γ (func d1f Margs) = appD1 d1f (`IMI γ Margs)
val⊢ γ (var v∈) = lookup γ v∈
val⊢ γ (contr {P = P} adr) = adr
val⊢ γ (m₁∈ ∸ₘ m₂∈) = lookup γ m₁∈ ∸ lookup γ m₂∈

modv : ∀ {Γ} → Int Γ → ∀ {t} → t ∈ Γ → ⟦ t ⟧ → Set
modv γ v x = lookup γ v ≡ x

-- Match models Int if all variables equal the corresponding values
-- modS stands for models Stack since Matches/Ints represent those
modS : ∀ {S Γ} → Int Γ → Match Γ S → Int S → Set
modS γ [] [] = ⊤
modS γ (v ∷ vs) (x ∷ xs) = (modv γ v x) × (modS γ vs xs)

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
_⊨φ_ : ∀ {Γ} → Int Γ → Formula Γ → Set
γ ⊨φ `false = ⊥
γ ⊨φ (v∈ := trm) = val∈ γ v∈ ≡ val⊢ γ trm
γ ⊨φ (x <ₘ x₁) = val∈ γ x < val∈ γ x₁
γ ⊨φ (x ≥ₘ x₁) = val∈ γ x ≥ val∈ γ x₁

modφ = _⊨φ_

-- lists of formulas always represent their conjunction, so each formula must be modeled
_⊨Φ_ : ∀ {Γ} → Int Γ → List (Formula Γ) → Set
γ ⊨Φ [] = ⊤
γ ⊨Φ [ φ // Φ ] = (γ ⊨φ φ) × (γ ⊨Φ Φ)

modΦ = _⊨Φ_

module alternative-mod-phi where

  modΦ′ : ∀ {Γ} → Int Γ → List (Formula Γ) → Set
  modΦ′ γ = All (modφ γ)

  modΦ⇒modΦ′ :  ∀ {Γ} → (γ : Int Γ) → (Φ : List (Formula Γ)) → modΦ γ Φ → modΦ′ γ Φ
  modΦ⇒modΦ′ γ [I] m = [I]
  modΦ⇒modΦ′ γ ([ x ]++ I) (φx , ΦI) = [ φx ]++ (modΦ⇒modΦ′ γ I ΦI)

  modΦ′⇒modΦ :  ∀ {Γ} → (γ : Int Γ) → (Φ : List (Formula Γ)) → modΦ′ γ Φ  → modΦ γ Φ
  modΦ′⇒modΦ γ [I] mΦ′ = tt
  modΦ′⇒modΦ γ ([ x ]++ Φ) ([ px ]++ mΦ′) = px , (modΦ′⇒modΦ γ Φ mΦ′)

MODELING : Context → (MODE → Set) → Set₁
MODELING Γ F = Abstract F Γ → Concrete F → Set

-- abstract contracts model concrete ones in an obvious way
-- modC : ∀ {Γ p s} → Int Γ → αContract Γ p s → CContract p s → Set

modC : ∀ {Γ p s} → Int Γ → MODELING Γ λ M → Contract M p s
modC γ (ctr αP αS αbalance αstorage αprogram) (ctr P S balance storage program)
  =        αP       ≡ P
  ×        αS       ≡ S
  × modv γ αbalance balance
  × modv γ αstorage storage
  ×        αprogram ≡ program

pattern modC⟨_,_⟩ x y = refl , refl , x , y , refl

-- subterm for modeling blockchains, models when types match and the contract is modeled
modMC : ∀ {Γ} → Int Γ → Maybe (∃[ αp ] ∃[ αs ] αContract Γ αp αs)
                      → Maybe (∃[  p ] ∃[  s ] CContract    p  s) → Set
modMC γ (just (αp , αs , αc)) (just (p , s , c))
  = Σ (αp ≡ p) λ{ refl → Σ (αs ≡ s) λ{ refl → modC γ αc c } }
modMC γ nothing nothing = ⊤
modMC γ _ _ = ⊥

-- ... don't know much else to say than Agda magic :D
-- ... yeah, sorry, can't explain it, but it makes sense, think about it ;)
-- modβ : ∀ {Γ} → Int Γ → βlockchain Γ → CBlockchain → Set

modβ : ∀ {Γ} → Int Γ → MODELING Γ Blockchain
modβ γ βl bl = ∀ a → modMC γ (βl a) (bl a)

------------------------- Environments and ⊎Program-states ------------------------------

-- environment modeling ... obvious
-- modE : ∀ {Γ} → Int Γ → αEnvironment Γ → CEnvironment → Set

modE : ∀ {Γ} → Int Γ → MODELING Γ Environment
modE γ (env αccounts αself αsender αbalance αamount)
       (env accounts  self  sender  balance  amount)
  = modβ γ αccounts accounts
  ×        αself ≡ self
  ×        αsender  ≡ sender
  × modv γ αbalance balance
  × modv γ αamount amount

pattern modE⟨_,_,_⟩ x y z = x , refl , refl , y , z

modins : ∀ {Γ ari ro} → Int Γ → MODELING Γ λ M → ShadowInst{MODE.𝓜 M} ari ro
modins γ (MPUSH1 x∈) (MPUSH1 v) = modv γ x∈ v


modprg : ∀ {Γ ari ro} → Int Γ → MODELING Γ λ M → ShadowProg{MODE.𝓜 M} ari ro
modprg γ end end = ⊤
modprg γ (_;_ {rn = arn} ains aprg) (_;_ {rn = crn} cins cprg) = Σ (arn ≡ crn) λ {refl → ains ≡ cins × modprg γ aprg cprg }
modprg γ (_∙_ {rn = arn} ains aprg) (_∙_  {rn = crn} cins cprg) = Σ (arn ≡ crn) λ{ refl → modins γ ains cins × modprg γ aprg cprg}
modprg γ _ _ = ⊥

modprg-extend : ∀ {Γ ri rn ro} (p : Program ri rn) → ∀ {aprg : ShadowProg rn ro} {cprg : ShadowProg rn ro}
  → {γ : Int Γ}
  → modprg γ aprg cprg
  → modprg γ (p ;∙ aprg) (p ;∙ cprg)
modprg-extend end mPRG = mPRG
modprg-extend (x ; p) mPRG = refl , refl , modprg-extend p mPRG

modprg-mpush : ∀ {Γ ri ro} {front} {astk : Match Γ front}{cstk : Int front}
  → ∀ {aprg : ShadowProg (front ++ ri) ro} {cprg : ShadowProg (front ++ ri) ro}
  → {γ : Int Γ}
  → modS γ astk cstk
  → modprg γ aprg cprg
  → modprg γ (mpush astk aprg) (mpush cstk cprg)
modprg-mpush {front = [I]} {([I])} {([I])} mS mPRG = mPRG
modprg-mpush {front = [ t ]++ front} {[ x∈ ]++ astk} {[ x ]++ cstk} (mv=x∈x , mS) mPRG
  = modprg-mpush mS (refl , (mv=x∈x , mPRG))

-- to model a program state, the output stacks will match implicitly by applying this
-- operator, but equality of the input stacks must be given explicitly
-- the rest is equality of the given programs and modelings of every subcomponent
-- modρ : ∀ {Γ} → Int Γ → αProg-state Γ ro so → CProg-state ro so → Set

modρ : ∀ {Γ} → Int Γ → MODELING Γ λ M → Prog-state M ro
modρ γ (state {ri = αri} αen αprg rVM Φ)
       (state {ri} en prg rSI tt)
  = Σ (αri ≡ ri) λ{ refl
    → modE γ αen en
    × modprg γ αprg prg
    × modS γ rVM rSI
    × modΦ γ Φ} 

pattern modρ⟨_,_,_,_⟩ x y mp z = refl , x , mp , y , z

-- a disjunction of program states is modeled if one of them is modeled
-- different approaches are possible but this one is most concise and efficient
mod⊎ρ : ∀ {Γ} → Int Γ → ⊎Prog-state ro → CProgState ro → Set
mod⊎ρ {Γ} γ ⊎ρ ρ = ∃[ αρ ] (Γ , αρ) ∈ ⊎ρ × modρ γ αρ ρ

