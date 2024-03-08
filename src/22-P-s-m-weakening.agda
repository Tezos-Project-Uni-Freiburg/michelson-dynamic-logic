
module 22-P-s-m-weakening where

open import 01-Types
open import 02-Functions-Interpretations
open import 03-concrete-execution
open import 11-abstract-representation-and-weakening
open import 12-abstract-execution-accessories-and-weakening
open import 21-Prog-state-modeling

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


------------------------- weakening of Values and Models -------------------------------
-- symbolic execution often extends the context, but most components don't change
-- except for being weakened
-- here we provide operators that provide modeling of such weakened components
-- as well as all the components for the symb. execution of PUSH
-- unfortunately "Agda magic" seems to be the best explanation here in general

wkval∈ : ∀ {Γ` Γ ty γ v∈} {γ` : Int Γ`} → val∈ (γ` +I+ γ) (wk∈ v∈) ≡ val∈ {ty} {Γ} γ v∈
wkval∈ {γ` = [I]} = refl
wkval∈ {γ` = x ∷ γ`} = wkval∈ {γ` = γ`}

wkIMI  : ∀ {Γ` Γ S M γ` γ} → IMI {Γ} {S} γ M ≡ IMI {Γ` ++ Γ} (γ` +I+ γ) (wkM M)
wkIMI  {M = [M]} = refl
wkIMI  {M = v∈ ∷ M} {γ`} = cong₂ _∷_ (sym (wkval∈ {γ` = γ`})) wkIMI

wkval⊢ : ∀ {Γ` ty Γ γ} {trm : Γ ⊢ ty} {γ` : Int Γ`}
       → val⊢ γ trm ≡ val⊢ (γ` +I+ γ) (wk⊢ trm)
wkval⊢ {trm = const x} = refl
wkval⊢ {trm = func d1f Margs} {γ`} = cong (appD1 d1f) (wkIMI {M = Margs} {γ`})
wkval⊢ {trm = var x} {γ`} = sym (wkval∈ {γ` = γ`})
wkval⊢ {trm = contr adr} = refl
wkval⊢ {γ = γ} {m₁∈ ∸ₘ m₂∈} {γ`}
  = sym (cong₂ _∸_ (wkval∈ {γ = γ} {m₁∈} {γ`}) (wkval∈ {γ = γ} {m₂∈} {γ`}))

wkmodS : ∀ {Γ` Γ γ S MS IS} {γ` : Int Γ`} → modS {S} {Γ} γ MS IS
       → modS (γ` +I+ γ) (wkM MS) IS
wkmodS {MS = [M]} {[I]} mS = tt
wkmodS {MS = v∈ ∷ MS} {x ∷ IS} {γ`} (v∈≡x , mS)
  = (trans (wkval∈ {γ` = γ`}) v∈≡x) , wkmodS mS

wkmodΦ : ∀ {Γ` Γ γ Φ} {γ` : Int Γ`} → modΦ {Γ} γ Φ → modΦ (γ` +I+ γ) (wkΦ {Γ`} Φ)
wkmodΦ {Φ = []} mΦ = tt
wkmodΦ {Φ = [ v∈ := trm // Φ ]} {γ`} (v∈≡trm , mΦ)
  = (trans (wkval∈ {γ` = γ`}) (trans v∈≡trm (wkval⊢ {trm = trm} {γ`}))) , wkmodΦ mΦ
wkmodΦ {γ = γ} {[ v∈ <ₘ w∈ // Φ ]} {γ`} (v∈<w∈ , mΦ)
  rewrite wkval∈ {γ = γ} {v∈} {γ`} | wkval∈ {γ = γ} {w∈} {γ`}
  = v∈<w∈ , (wkmodΦ mΦ)
wkmodΦ {γ = γ} {[ v∈ ≥ₘ w∈ // Φ ]} {γ`} (v∈≥w∈ , mΦ)
  rewrite wkval∈ {γ = γ} {v∈} {γ`} | wkval∈ {γ = γ} {w∈} {γ`}
  = v∈≥w∈ , (wkmodΦ mΦ)

------------------------- expansion of complex constants --------------------------------

createγ : ∀ {ty} → (P : Pushable ty) → (x : ⟦ ty ⟧) → Int (expandΓ P x)
createγ (base bt) x = x ∷ [I]
createγ (pair P₁ P₂) x@(x₁ , x₂) = x ∷ (createγ P₁ x₁ +I+ createγ P₂ x₂)
createγ (list P) [] = [] ∷ [I]
createγ (list P) xxs@([ x // xs ]) = xxs ∷ (createγ P x +I+ createγ (list P) xs)
createγ (option P) nothing = nothing ∷ [I]
createγ (option P) ox@(just x) = ox ∷ createγ P x

val0∈exΓ : ∀ {ty} → (P : Pushable ty) → (x : ⟦ ty ⟧) → val∈ (createγ P x) (0∈exΓ P) ≡ x
val0∈exΓ (base bt) x = refl
val0∈exΓ (pair P P₁) (fst , snd) = refl
val0∈exΓ (list P) [] = refl
val0∈exΓ (list P) [ x // x₁ ] = refl
val0∈exΓ (option P) nothing = refl
val0∈exΓ (option P) (just x) = refl

_+modΦ+_ : ∀ {Γ} {γ : Int Γ} {Φ₁ Φ₂} → modΦ γ Φ₁ → modΦ γ Φ₂ → modΦ γ (Φ₁ ++ Φ₂)
_+modΦ+_ {Φ₁ = []} mΦ₁ mΦ₂ = mΦ₂
_+modΦ+_ {Φ₁ = [ φ // Φ₁ ]} (mφ , mΦ₁) mΦ₂ = mφ , (mΦ₁ +modΦ+ mΦ₂)

val∈wk : ∀ {Γ` Γ ty} {γ` : Int Γ`} {γ : Int Γ} {v∈ : ty ∈ Γ}
       → val∈ (γ +I+ γ`) (∈wk v∈) ≡ val∈ γ v∈
val∈wk {γ = x ∷ γ} {here refl} = refl
val∈wk {γ = x ∷ γ} {there v∈} = val∈wk {γ = γ} {v∈}

IMIwk  : ∀ {Γ` Γ S} {γ : Int Γ} {M : Match Γ S} {γ` : Int Γ`}
       → IMI γ M ≡ IMI (γ +I+ γ`) (Mwk M)
IMIwk  {M = [M]} = refl
IMIwk  {γ = γ} {v∈ ∷ M} {γ`} = cong₂ _∷_ (sym (val∈wk {γ = γ})) IMIwk

val⊢wk : ∀ {Γ` ty Γ γ} {trm : Γ ⊢ ty} {γ` : Int Γ`}
       → val⊢ γ trm ≡ val⊢ (γ +I+ γ`) (⊢wk trm)
val⊢wk {trm = const x} = refl
val⊢wk {γ = γ} {func d1f Margs} = cong (appD1 d1f) (IMIwk {γ = γ} {Margs})
val⊢wk {γ = γ} {var x} = sym (val∈wk {γ = γ})
val⊢wk {trm = contr adr} = refl
val⊢wk {γ = γ} {m₁∈ ∸ₘ m₂∈} {γ`}
  = sym (cong₂ _∸_ (val∈wk {γ` = γ`} {γ} {m₁∈}) (val∈wk {γ` = γ`} {γ} {m₂∈}))

modΦwk : ∀ {Γ` Γ} {γ` : Int Γ`} {γ : Int Γ} {Φ : List (Formula Γ)}
       → modΦ γ Φ → modΦ (γ +I+ γ`) (Φwk Φ)
modΦwk {Φ = []} mΦ = tt
modΦwk {γ = γ} {Φ = [ v∈ := trm // Φ ]} (v∈≡trm , mΦ)
  = (trans (val∈wk {γ = γ}) (trans v∈≡trm (val⊢wk {γ = γ} {trm}))) , modΦwk mΦ
modΦwk {γ` = γ`} {γ} {[ v∈ <ₘ w∈ // Φ ]} (v∈<w∈ , mΦ)
  rewrite val∈wk {γ` = γ`} {γ} {v∈} | val∈wk {γ` = γ`} {γ} {w∈}
  = v∈<w∈ , (modΦwk mΦ)
modΦwk {γ` = γ`} {γ} {[ v∈ ≥ₘ w∈ // Φ ]} (v∈≥w∈ , mΦ)
  rewrite val∈wk {γ` = γ`} {γ} {v∈} | val∈wk {γ` = γ`} {γ} {w∈}
  = v∈≥w∈ , (modΦwk mΦ)

modunfoldΦ : ∀ {ty} → (P : Pushable ty) → (x : ⟦ ty ⟧) → modΦ (createγ P x) (unfold P x)
modunfoldΦ (base bt) x = refl , tt
modunfoldΦ (pair P P₁) (x , x₁)
  rewrite val∈wk {γ` = createγ P₁ x₁} {createγ P x} {0∈exΓ P}  | val0∈exΓ P  x
        | wkval∈ {γ  = createγ P₁ x₁} {0∈exΓ P₁} {createγ P x} | val0∈exΓ P₁ x₁
  = refl
  , wkmodΦ {γ` = _ ∷ [I]} (modΦwk (modunfoldΦ P x) +modΦ+ wkmodΦ (modunfoldΦ P₁ x₁))
modunfoldΦ (list P) [] = refl , tt
modunfoldΦ (list P) [ x // xs ]
  rewrite val∈wk {γ` = createγ (list P) xs} {createγ P x} {0∈exΓ P} | val0∈exΓ P x
        | wkval∈ {γ  = createγ (list P) xs} {0∈exΓ (list P)} {createγ P x}
        | val0∈exΓ (list P) xs
  = refl , wkmodΦ {γ` = _ ∷ [I]}
                  (modΦwk (modunfoldΦ P x) +modΦ+ wkmodΦ (modunfoldΦ (list P) xs))
modunfoldΦ (option P) nothing = refl , tt
modunfoldΦ (option P) (just x) rewrite val0∈exΓ P x = refl , wkmodΦ (modunfoldΦ P x)

wkmodC : ∀ {Γ` Γ p s γ γ` αc c} → modC {Γ} {p} {s} γ αc c
       → modC {Γ` ++ Γ} (γ` +I+ γ) (wkC αc) c
wkmodC {γ` = γ`} (refl , refl , refl , refl , refl)
  = refl , refl , wkval∈ {γ` = γ`} , wkval∈ {γ` = γ`} , refl

wkmodMC : ∀ {Γ` Γ γ γ` Mpsαc Mpsc} → modMC {Γ} γ Mpsαc Mpsc
        → modMC {Γ` ++ Γ} (γ` +I+ γ) (wkMC Mpsαc) Mpsc
-- wkmodMC {γ` = γ`} {just (αp , αs , αc)} {just (.αp , s , c)} (refl , ss,mC) = {!!}
wkmodMC {γ` = γ`} {just (p , s , αc)} {just (.p , .s , c)} (refl , refl , mC)
  = refl , refl , (wkmodC {γ` = γ`} mC)
wkmodMC {γ` = γ`} {nothing} {nothing} mMC = tt

wkmodβ : ∀ {Γ` Γ γ` γ βl bl} → modβ {Γ} γ βl bl
       → modβ {Γ` ++ Γ} (γ` +I+ γ) (wkβ βl) bl
wkmodβ mβ a = wkmodMC (mβ a)
{-
wkmodβ {γ` = γ`} {βl = βl} {bl} mβ a with βl a | bl a | mβ a
... | just αx | just x | refl , refl , refl , refl , refl , refl , refl
  = refl , refl , refl , refl , wkval∈ {γ` = γ`} , wkval∈ {γ` = γ`} , refl
-- ... | just αc | just c | mMC =
... | nothing | nothing | tt = tt
-}

wkmodE : ∀ {Γ` Γ γ` γ αen en} → modE {Γ} γ αen en
       → modE {Γ` ++ Γ} (γ` +I+ γ) (wkαE αen) en
wkmodE {γ` = γ`} (macts , refl , refl , refl , refl)
  = wkmodβ macts
  , refl , refl , wkval∈ {γ` = γ`} , wkval∈ {γ` = γ`}

{-

------------------------- for abstract app of environment functions ---------------------
... which i don't use anymore since most of my current abstract environment functions
    just puts existing variables onto the stack

modαappEF : ∀ {args result Γ αe en} {γ : Int Γ} {ef : env-func args result} {Margs : Match Γ args} {Iargs : Int args}
          → modEnv γ αe en → modS γ Margs Iargs → modφ (appEF ef en Iargs ∷ γ) (αappEF ef αe Margs)
modαappEF {ef = AMOUNT}  {[M]} {[I]} (refl , refl) tt = refl
modαappEF {ef = BALANCE} {[M]} {[I]} (refl , refl) tt = refl
-}

------------------------- for FOL⇒ and special-case -------------------------------------

modφ∈Φ : ∀ {Γ γ φ Φ} → φ ∈ Φ → modΦ {Γ} γ Φ → modφ γ φ
modφ∈Φ (here refl) (mφ , mΦ) = mφ
modφ∈Φ (there φ∈) (mφ` , mΦ) = modφ∈Φ φ∈ mΦ

{-
modφ∷=φ` : ∀ {Γ γ φ φ` Φ} → (φ∈ : φ ∈ Φ) → modφ {Γ} γ φ` → modΦ γ Φ → modΦ γ (φ∈ ∷= φ`)
modφ∷=φ` (here px)  mφ` (mφ , mΦ) = mφ` , mΦ
modφ∷=φ` (there φ∈) mφ` (mψ , mΦ) = mψ , modφ∷=φ` φ∈ mφ` mΦ

proj₁≡ : ∀ {x y z} {p : A × B} → x ≡ proj₁ p → p ≡ (y , z) → x ≡ y
proj₁≡ refl refl = refl
proj₂≡ : ∀ {x y z} {p : A × B} → x ≡ proj₂ p → p ≡ (y , z) → x ≡ z
proj₂≡ refl refl = refl

IMIgetM≡getI : ∀ {Γ Φ γ S} (MC : MatchConst Φ S) → modΦ {Γ} γ Φ → IMI γ (getMatch MC) ≡ getInt MC
IMIgetM≡getI [MC] mΦ = refl
IMIgetM≡getI (v∈=C∈Φ ∷ MC) mΦ with modφ∈Φ v∈=C∈Φ mΦ
... | v∈≡C  = cong₂ _∷_ v∈≡C (IMIgetM≡getI MC mΦ)

-}

