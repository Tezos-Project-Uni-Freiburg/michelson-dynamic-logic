
module 11-abstract-representation-and-weakening where

open import 01-Types
open import 02-Functions-Interpretations
open import 03-concrete-execution

open import Level
open import Relation.Binary.PropositionalEquality hiding ([_])

open import Data.Nat hiding (_/_)
open import Data.List.Base hiding ([_]; unfold)
open import Data.Maybe.Base
open import Data.Product

open import Data.List.Relation.Unary.Any
open import Data.List.Membership.Propositional


pattern 0∈ = here refl
pattern 1∈ = there (here refl)
pattern 2∈ = there (there (here refl))
pattern 3∈ = there (there (there (here refl)))
pattern 4∈ = there (there (there (there (here refl))))
pattern 5∈ = there (there (there (there (there (here refl)))))
pattern 6∈ = there (there (there (there (there (there (here refl))))))
pattern 7∈ = there (there (there (there (there (there (there (here refl)))))))
pattern 8∈ = there (there (there (there (there (there (there (there (here refl))))))))
pattern 9∈ = there (there (there (there (there (there (there (there (there (here refl)
                   ))))))))

infixr 15 10+_
pattern 10+_ v∈ = there (there (there (there (there (there (there (there (there
                        (there v∈)))))))))

------------------------- Variables and Matches -----------------------------------------

-- test

private
  variable
    a : Level
    A : Set a

2+ : ∀ {xs : List A}{x y z} → x ∈ xs → x ∈ y ∷ z ∷ xs
2+ x∈ = there (there x∈)

del : ∀ {x : A}{xs} → x ∈ xs → List A
del (here {xs = xs} px) = xs
del (there {x} x∈xs) = x ∷ del x∈xs

infix  09 _∷=_/_
_∷=_/_ : ∀ {x : A}{xs} → x ∈ xs → A → A → List A
here {xs = xs} px ∷= y / z = [ y / z // xs ]
there {x} x∈xs ∷= y / z = [ x // x∈xs ∷= y / z ]

Context = List Type

infixr 5 _∷_
data Match (Γ : Context) : Stack → Set where
  [M]  : Match Γ []
  _∷_ : ∀ {ty S} → (v∈ : ty ∈ Γ) → Match Γ S → Match Γ (ty ∷ S)

Mtop : ∀ {top S Γ} → Match Γ (top ++ S) → Match Γ top
Mtop {[]} μ = [M]
Mtop {[ ty // top ]} (v∈ ∷ μ) = v∈ ∷ Mtop {top} μ

Mbot : ∀ {top S Μ} → Match Μ (top ++ S) → Match Μ S
Mbot {[]} μ = μ
Mbot {[ ty // top ]} (v∈ ∷ μ) = Mbot {top} μ

takeM : ∀ {Γ S} n → Match Γ S → Match Γ (take n S)
takeM zero M = [M]
takeM (suc n) [M] = [M]
takeM (suc n) (v∈ ∷ M) = v∈ ∷ (takeM n M)

dropM : ∀ {Γ S} n → Match Γ S → Match Γ (drop n S)
dropM zero M = M
dropM (suc n) [M] = [M]
dropM (suc n) (v∈ ∷ M) = dropM n M

_+M+_ : ∀ {top S Γ} → Match Γ top → Match Γ S → Match Γ (top ++ S)
[M] +M+ μ = μ
(v∈ ∷ μtop) +M+ μ = v∈ ∷ μtop +M+ μ

------------------------- Terms and Formulas --------------------------------------------

data _⊢_ (Γ : Context)    : Type → Set where
  const : ∀ {bt}          → ⟦ base bt ⟧               → Γ ⊢ base bt
  func  : ∀ {args result} → 1-func args result
                          → Match Γ args              → Γ ⊢ result
  var   : ∀ {ty}          → ty ∈ Γ                    → Γ ⊢ ty
  contr : ∀ {ty P}        → ⟦ contract {ty} P ⟧       → Γ ⊢ contract P
  _∸ₘ_  : base mutez ∈ Γ  → base mutez ∈ Γ            → Γ ⊢ base mutez

infix  10 _:=_
infix  10 _<ₘ_
infix  10 _≥ₘ_
data Formula (Γ : Context) : Set where
  `false : Formula Γ
  _:=_   : ∀ {ty} → ty ∈ Γ → Γ ⊢ ty   →  Formula Γ
  _<ₘ_   : base mutez ∈ Γ → base mutez ∈ Γ   →  Formula Γ
  _≥ₘ_   : base mutez ∈ Γ → base mutez ∈ Γ   →  Formula Γ
  
------------------------- weakening lemmata for abstract execution ----------------------

wk∈ : ∀ {Γ` Γ} {ty : A} → ty ∈ Γ → ty ∈ Γ` ++ Γ
wk∈ {Γ` = []} v∈ = v∈
wk∈ {Γ` = [ t // Γ` ]} v∈ = there (wk∈ v∈)

∈wk : ∀ {Γ` Γ} {ty : A} → ty ∈ Γ → ty ∈ Γ ++ Γ`
∈wk (here px) = here px
∈wk (there v∈) = there (∈wk v∈)

wkM : ∀ {Γ` Γ S} → Match Γ S → Match (Γ` ++ Γ) S
wkM [M] = [M]
wkM (v∈ ∷ MS) = (wk∈ v∈) ∷ (wkM MS)

Mwk : ∀ {Γ` Γ S} → Match Γ S → Match (Γ ++ Γ`) S
Mwk [M] = [M]
Mwk (v∈ ∷ MS) = (∈wk v∈) ∷ (Mwk MS)

wk⊢ : ∀ {Γ` Γ t} → Γ ⊢ t → (Γ` ++ Γ) ⊢ t
wk⊢ (const x) = const x
wk⊢ (func ft Margs) = func ft (wkM Margs)
wk⊢ (var v∈) = var (wk∈ v∈)
wk⊢ (contr c) = contr c
wk⊢ (m₁∈ ∸ₘ m₂∈) = wk∈ m₁∈ ∸ₘ wk∈ m₂∈

⊢wk : ∀ {Γ` Γ ty} → Γ ⊢ ty → (Γ ++ Γ`) ⊢ ty
⊢wk (const x) = const x
⊢wk (func d1f Margs) = func d1f (Mwk Margs)
⊢wk (var v∈) = var (∈wk v∈)
⊢wk (contr c) = contr c
⊢wk (m₁∈ ∸ₘ m₂∈) = ∈wk m₁∈ ∸ₘ ∈wk m₂∈


wkΦ : ∀ {Γ` Γ} → List (Formula Γ) → List (Formula (Γ` ++ Γ))
wkΦ [] = []
wkΦ [ `false // Φ ] = [ `false // wkΦ Φ ]
wkΦ [ v∈ := trm // Φ ] = [ wk∈ v∈ := wk⊢ trm // wkΦ Φ ]
wkΦ [ m₁∈ <ₘ m₂∈ // Φ ] = [ wk∈ m₁∈ <ₘ wk∈ m₂∈ // wkΦ Φ ]
wkΦ [ m₁∈ ≥ₘ m₂∈ // Φ ] = [ wk∈ m₁∈ ≥ₘ wk∈ m₂∈ // wkΦ Φ ]

Φwk : ∀ {Γ` Γ} → List (Formula Γ) → List (Formula (Γ ++ Γ`))
Φwk [] = []
Φwk [ `false // Φ ] = [ `false // Φwk Φ ]
Φwk [ v∈ := trm // Φ ] = [ ∈wk v∈ := ⊢wk trm // Φwk Φ ]
Φwk [ m₁∈ <ₘ m₂∈ // Φ ] = [ ∈wk m₁∈ <ₘ ∈wk m₂∈ // Φwk Φ ]
Φwk [ m₁∈ ≥ₘ m₂∈ // Φ ] = [ ∈wk m₁∈ ≥ₘ ∈wk m₂∈ // Φwk Φ ]

------------------------- Expanding values of complex Types -----------------------------

expandΓ : ∀ {ty} → Pushable ty → ⟦ ty ⟧ → Context
expandΓ (base    bt)               x           = [ base bt ]
expandΓ (list   {ty}        P)     []          = [ list ty ]
expandΓ (option {ty}        P)     nothing     = [ option ty ]
expandΓ (option {ty}        P)     (just x)    = [ option ty // expandΓ P  x  ]
expandΓ (pair   {ty₁} {ty₂} P₁ P₂) (x₁ , x₂)
  = [ pair ty₁ ty₂ // expandΓ P₁ x₁ ++ expandΓ P₂ x₂ ]
expandΓ (list   {ty}        P)     [ x // xs ]
  = [ list ty // expandΓ P  x  ++ expandΓ (list P) xs ]

0∈exΓ : ∀ {ty} → (P : Pushable ty) → {x : ⟦ ty ⟧} → ty ∈ expandΓ P x
0∈exΓ (base bt) = 0∈
0∈exΓ (pair P₁ P₂) = 0∈
0∈exΓ (list P) {[]} = 0∈
0∈exΓ (list P) {[ x // xs ]} = 0∈
0∈exΓ (option P) {just x}  = 0∈
0∈exΓ (option P) {nothing} = 0∈

unfold : ∀ {ty} → (P : Pushable ty) → (x : ⟦ ty ⟧) → List (Formula (expandΓ P x))
unfold (base bt) x = [ 0∈ := const x ]
unfold (pair P₁ P₂) (x₁ , x₂)
  = [  0∈ := func PAIR (there (∈wk (0∈exΓ P₁)) ∷
                        there (wk∈ (0∈exΓ P₂)) ∷ [M])
              // wkΦ {[ _ ]} ((Φwk (unfold P₁ x₁)) ++ wkΦ (unfold P₂ x₂)) ]
unfold {list ty} (list P) [] = [ 0∈ := func (NIL ty) [M] ]
unfold (list P) [ x // xs ]
  = [  0∈ := func CONS (there (∈wk (0∈exΓ P)) ∷
                        there (wk∈ (0∈exΓ (list P) {xs})) ∷ [M])
    // wkΦ {[ _ ]} ((Φwk (unfold P x)) ++ wkΦ (unfold (list P) xs)) ]
unfold (option P) (just x)
  = [ 0∈ := func SOME ((there (0∈exΓ P)) ∷ [M]) // wkΦ (unfold P x) ]
unfold {option ty} (option P) nothing = [ 0∈ := func (NONE ty) [M] ]

