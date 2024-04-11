
module 22-2-P-s-m-weakening where

import 00-All-Utilities as H

open import 01-Types
open import 02-Functions-Interpretations
open import 03-2-concrete-execution
open import 11-abstract-representation-and-weakening
open import 12-2-abstract-execution-accessories-and-weakening
open import 21-2-Prog-state-modeling

open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import Data.Nat
open import Data.List.Base hiding ([_]; unfold; map)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product hiding (map)
open import Data.Sum hiding (map)
open import Data.Unit
open import Data.Empty

open import Data.List.Relation.Unary.All
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Membership.Propositional using (_∈_)


------------------------- weakening of Values and Models -------------------------------
-- symbolic execution often extends the context, but most components don't change
-- except for being weakened
-- here we provide operators that provide modeling of such weakened components
-- as well as all the components for the symb. execution of `PUSH
-- unfortunately "Agda magic" seems to be the best explanation here in general

wkval∈ : ∀ {Γ` Γ ty} {γ : Int Γ} {v∈ : ty ∈ Γ} {γ` : Int Γ`} → val∈ (γ` +I+ γ) (wk∈ v∈) ≡ val∈ {Γ} γ {ty} v∈
wkval∈ {γ` = []} = refl
wkval∈ {γ` = x ∷ γ`} = wkval∈ {γ` = γ`}

wk`IMI  : ∀ {Γ` Γ S M γ` γ} → `IMI {Γ} {S} γ M ≡ `IMI {Γ` ++ Γ} (γ` +I+ γ) (wkM M)
wk`IMI  {M = [M]} = refl
wk`IMI  {M = v∈ ∷ M} {γ`}{γ} = cong₂ _∷_ (sym (wkval∈ {γ` = γ`})) (wk`IMI {γ` = γ`}{γ = γ})

wkval⊢ : ∀ {Γ` ty Γ γ} {trm : Γ ⊢ ty} {γ` : Int Γ`}
       → val⊢ γ trm ≡ val⊢ (γ` +I+ γ) (wk⊢ trm)
wkval⊢ {trm = const x} = refl
wkval⊢ {trm = func d1f Margs} {γ`} = cong (appD1 d1f) (wk`IMI {M = Margs} {γ`})
wkval⊢ {trm = var x} {γ`} = sym (wkval∈ {γ` = γ`})
wkval⊢ {trm = contr adr} = refl
wkval⊢ {γ = γ} {m₁∈ ∸ₘ m₂∈} {γ`}
  = sym (cong₂ _∸_ (wkval∈ {γ = γ} {m₁∈} {γ`}) (wkval∈ {γ = γ} {m₂∈} {γ`}))

wkmodS : ∀ {Γ` Γ γ S `MS `IS} {γ` : Int Γ`} → modS {S} {Γ} γ `MS `IS
       → modS (γ` +I+ γ) (wkM `MS) `IS
wkmodS {`MS = [M]} {[I]} mS = tt
wkmodS {`MS = v∈ ∷ `MS} {x ∷ `IS} {γ`} (v∈≡x , mS)
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

-- ------------------------- expansion of complex constants --------------------------------

createγ : ∀ {ty} → (P : Pushable ty) → (x : ⟦ ty ⟧) → Int (expandΓ P x)
createγ (base bt) x = x ∷ []
createγ (pair P₁ P₂) x@(x₁ , x₂) = x ∷ (createγ P₁ x₁ H.++ createγ P₂ x₂)
createγ (list P) [] = [] ∷ []
createγ (list P) xxs@([ x // xs ]) = xxs ∷ (createγ P x H.++ createγ (list P) xs)
createγ (option P) nothing = nothing ∷ []
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

`IMIwk  : ∀ {Γ` Γ S} {γ : Int Γ} {M : Match Γ S} {γ` : Int Γ`}
       → `IMI γ M ≡ `IMI (γ +I+ γ`) (Mwk M)
`IMIwk  {M = [M]} = refl
`IMIwk  {γ = γ} {v∈ ∷ M} {γ`} = cong₂ _∷_ (sym (val∈wk {γ = γ})) ( `IMIwk {γ = γ}{γ` = γ`}) -- `IMIwk

val⊢wk : ∀ {Γ` ty Γ γ} {trm : Γ ⊢ ty} {γ` : Int Γ`}
       → val⊢ γ trm ≡ val⊢ (γ +I+ γ`) (⊢wk trm)
val⊢wk {trm = const x} = refl
val⊢wk {γ = γ} {func d1f Margs} = cong (appD1 d1f) (`IMIwk {γ = γ} {Margs})
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
modunfoldΦ (pair P₁ P₂) x@(x₁ , x₂)
  -- rewrite val∈wk {γ` = createγ P₁ x₁} {createγ P x} {0∈exΓ P}  | val0∈exΓ P  x
  --       | wkval∈ {γ  = createγ P₁ x₁} {0∈exΓ P₁} {createγ P x} | val0∈exΓ P₁ x₁
  = cong₂ _,_
    (begin
      x₁
    ≡⟨ sym (val0∈exΓ P₁ x₁) ⟩
      val∈ (createγ P₁ x₁) (0∈exΓ P₁)
    ≡⟨ sym (val∈wk {γ` = createγ P₂ x₂}{γ = createγ P₁ x₁} {0∈exΓ P₁}) ⟩
      val∈ (createγ P₁ x₁ H.++ createγ P₂ x₂) (∈wk (0∈exΓ P₁))
    ≡⟨ refl ⟩
      val∈ (x ∷ (createγ P₁ x₁ H.++ createγ P₂ x₂)) (there (∈wk (0∈exΓ P₁)))
    ≡⟨ refl ⟩
      val∈ (createγ (pair P₁ P₂) (x₁ , x₂)) (there (∈wk (0∈exΓ P₁)))
    ∎)
    (begin
      x₂
    ≡⟨ sym (val0∈exΓ P₂ x₂) ⟩
      val∈ (createγ P₂ x₂) (0∈exΓ P₂)
    ≡⟨ sym (wkval∈ {γ = createγ P₂ x₂} {v∈ = 0∈exΓ P₂} {γ` = createγ P₁ x₁}) ⟩
      val∈ ( createγ P₁ x₁ H.++ createγ P₂ x₂) ( wk∈ (0∈exΓ P₂))
    ≡⟨ refl ⟩
      val∈ (x ∷ createγ P₁ x₁ H.++ createγ P₂ x₂) (there (wk∈ (0∈exΓ P₂)))
    ≡⟨ refl ⟩
      val∈ (createγ (pair P₁ P₂) (x₁ , x₂)) (there (wk∈ (0∈exΓ P₂)))
    ∎)
  , wkmodΦ {γ` = _ ∷ [I]} (modΦwk (modunfoldΦ P₁ x₁) +modΦ+ wkmodΦ (modunfoldΦ P₂ x₂))
modunfoldΦ (list P) [] = refl , tt
modunfoldΦ (list P) [ x // xs ]
  -- rewrite val∈wk {γ` = createγ (list P) xs} {createγ P x} {0∈exΓ P} | val0∈exΓ P x
  --       | wkval∈ {γ  = createγ (list P) xs} {0∈exΓ (list P)} {createγ P x}
  --       | val0∈exΓ (list P) xs
  = (begin
      (x ∷ xs)
    ≡⟨ cong₂ _∷_
      (begin
        x
      ≡⟨ sym (val0∈exΓ P x) ⟩
        val∈ (createγ P x) (0∈exΓ P)
      ≡⟨ sym (val∈wk {γ` = createγ (list P) xs}{γ = createγ P x} {0∈exΓ P})  ⟩
        val∈ ( createγ P x H.++ createγ (list P) xs) ( ∈wk (0∈exΓ P))
      ≡⟨ refl ⟩
        val∈ ([ x ∷ xs ]++ (createγ P x H.++ createγ (list P) xs))
          (there (∈wk (0∈exΓ P)))
      ∎)
      (begin
        xs
      ≡⟨ sym (val0∈exΓ (list P) xs) ⟩
        val∈ (createγ (list P) xs) (0∈exΓ (list P))
      ≡⟨ sym (wkval∈ {γ = createγ (list P) xs} {v∈ = 0∈exΓ (list P)} {γ` = createγ P x}) ⟩
        val∈ ([ x ∷ xs ]++ (createγ P x H.++ createγ (list P) xs))
          (there (wk∈ (0∈exΓ (list P) {x = xs})))
      ∎)
      ⟩
      val⊢ (createγ (list P) ([ x ]++ xs))
        (func `CONS
         [ there (∈wk (0∈exΓ P)) ⨾ there (wk∈ (0∈exΓ (list P) {x = xs})) ])
    ∎)
    , wkmodΦ {γ` = _ ∷ [I]}
                  (modΦwk (modunfoldΦ P x) +modΦ+ wkmodΦ (modunfoldΦ (list P) xs))
modunfoldΦ (option P) nothing = refl , tt
modunfoldΦ (option P) (just x)
  -- rewrite val0∈exΓ P x
  = cong just (sym (val0∈exΓ P x))
  , wkmodΦ (modunfoldΦ P x)

wkmodC : ∀ {Γ` Γ p s γ γ` αc c} → modC {Γ} {p} {s} γ αc c
       → modC {Γ` ++ Γ} (γ` +I+ γ) (wkC αc) c
wkmodC  {γ` = γ`} modC⟨ refl , refl ⟩
  = modC⟨ wkval∈ {γ` = γ`} , wkval∈ {γ` = γ`} ⟩

-- wkmodC {γ` = γ`} (refl , refl , refl , refl , refl)
--   = refl , refl , wkval∈ {γ` = γ`} , wkval∈ {γ` = γ`} , refl

wkmodMC : ∀ {Γ` Γ γ γ` Mpsαc Mpsc} → modMC {Γ} γ Mpsαc Mpsc
        → modMC {Γ` ++ Γ} (γ` +I+ γ) (wk`MC Mpsαc) Mpsc
-- wkmodMC {γ` = γ`} {just (αp , αs , αc)} {just (.αp , s , c)} (refl , ss,mC) = {!!}
wkmodMC {γ` = γ`} {just (p , s , αc)} {just (.p , .s , c)} (refl , refl , mC)
  = refl , refl , (wkmodC {γ` = γ`} mC)
wkmodMC {γ` = γ`} {nothing} {nothing} m`MC = tt

wkmodβ : ∀ {Γ` Γ γ` γ βl bl} → modβ {Γ} γ βl bl
       → modβ {Γ` ++ Γ} (γ` +I+ γ) (wkβ βl) bl
wkmodβ mβ a = wkmodMC (mβ a)
{-
wkmodβ {γ` = γ`} {βl = βl} {bl} mβ a with βl a | bl a | mβ a
... | just αx | just x | refl , refl , refl , refl , refl , refl , refl
  = refl , refl , refl , refl , wkval∈ {γ` = γ`} , wkval∈ {γ` = γ`} , refl
-- ... | just αc | just c | m`MC =
... | nothing | nothing | tt = tt
-}

wkmodE : ∀ {Γ` Γ γ` γ αen en} → modE {Γ} γ αen en
       → modE {Γ` ++ Γ} (γ` +I+ γ) (wkαE αen) en
wkmodE {γ` = γ`} modE⟨ macts , refl , refl ⟩
  = modE⟨ wkmodβ macts , wkval∈ {γ` = γ`} , wkval∈ {γ` = γ`} ⟩
-- wkmodE {γ` = γ`} (macts , refl , refl , refl , refl)
--   = wkmodβ macts
--   , refl , refl , wkval∈ {γ` = γ`} , wkval∈ {γ` = γ`}


wkmodins : ∀ {Γ` Γ γ` γ}{ari ro}{ αins : ShadowInst ari ro }{ ins : ShadowInst ari ro} → modins {Γ} γ αins ins
       → modins {Γ` ++ Γ} (γ` +I+ γ) (wkSI αins) ins
wkmodins {γ` = γ`}{γ = γ} {αins = MPUSH1 x∈} {ins = MPUSH1 x} refl = wkval∈ {v∈ = x∈}{γ`}

wkmodprg : ∀ {Γ` Γ γ` γ}{ari ro}{ αprg : ShadowProg ari ro }{ prg : ShadowProg ari ro} → modprg {Γ} γ αprg prg
       → modprg {Γ` ++ Γ} (γ` +I+ γ) (wkSP αprg) prg
wkmodprg {αprg = end} {prg = end} mPRG = tt
wkmodprg {αprg = x ; αprg} {prg = x₁ ; prg} (refl , refl , mPRG) = refl , refl , wkmodprg mPRG
wkmodprg {αprg = x ∙ αprg} {prg = x₁ ∙ prg} (refl , mINS , mPRG) = refl , (wkmodins mINS , wkmodprg mPRG)

------------------------- for `FOL⇒ and special-case -------------------------------------

modφ∈Φ : ∀ {Γ γ φ Φ} → φ ∈ Φ → modΦ {Γ} γ Φ → modφ γ φ
modφ∈Φ (here refl) (mφ , mΦ) = mφ
modφ∈Φ (there φ∈) (mφ` , mΦ) = modφ∈Φ φ∈ mΦ

