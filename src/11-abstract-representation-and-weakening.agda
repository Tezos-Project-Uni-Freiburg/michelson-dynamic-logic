
module 11-abstract-representation-and-weakening where

open import 01-Types
open import 02-Functions-Interpretations
open import 03-concrete-execution

open import Level
open import Relation.Binary.PropositionalEquality hiding ([_])

open import Data.Nat hiding (_/_)
open import Data.List using (List; []; _∷_; map; _++_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)

open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
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

private
  variable
    a : Level
    A : Set a

-- small helper functions to easily manipulate list elements for symbolic execution

2+ : ∀ {xs : List A}{x y z} → x ∈ xs → x ∈ y ∷ z ∷ xs
2+ x∈ = there (there x∈)

del : ∀ {x : A}{xs} → x ∈ xs → List A
del (here {xs = xs} px) = xs
del (there {x} x∈xs) = x ∷ del x∈xs

-- replacing a list element with 2 new elements
infix  09 _∷=_/_
_∷=_/_ : ∀ {x : A}{xs} → x ∈ xs → A → A → List A
here {xs = xs} px ∷= y / z = [ y / z // xs ]
there {x} x∈xs ∷= y / z = [ x // x∈xs ∷= y / z ]

Context = List Type

-- a Match is how the stack is represented during symbolic execution
-- and also how functional terms are defined (more on that later...)
-- it's another list like data structure that implements everything that was already
-- implemented for Int in exactly the same way
-- infixr 5 _∷_
-- data Match (Γ : Context) : Stack → Set where
--   [M]  : Match Γ []
--   _∷_ : ∀ {ty S} → (v∈ : ty ∈ Γ) → Match Γ S → Match Γ (ty ∷ S)

Match : Context → Stack → Set
Match Γ = All (_∈ Γ)

pattern [M] = []


------------------------- Terms and Formulas --------------------------------------------

-- terms under the context Γ of a given type are either constants of primitive types
-- or functions of a list of variables from the context (hence 1D functions play an
-- important role)
-- var i think is on longer used, contr is like a constant term but for a non
-- primitive type, and _∸ₘ_ is to express transaction fees in case not all values are
-- known
data _⊢_ (Γ : Context)    : Type → Set where
  const  : ⟦ base bt ⟧        → Γ ⊢ base bt
  func   : 1-func args result → Match Γ args → Γ ⊢ result
  var    : t ∈ Γ              → Γ ⊢ t
  contr  : ∀ {P : Passable t} → ⟦ contract P ⟧ → Γ ⊢ contract P
  _∸ₘ_   : mutez ∈ Γ → mutez ∈ Γ → Γ ⊢ mutez

infix  10 _:=_
infix  10 _<ₘ_
infix  10 _≥ₘ_
-- `false is also a relic but was important in an earlier version as explained in the
-- thesis, and the mutez comparisons are for the same case as _∸ₘ_ (more details later)
data Formula (Γ : Context) : Set where
  `false  : Formula Γ
  _:=_    : t ∈ Γ → Γ ⊢ t →  Formula Γ
  _<ₘ_    : mutez ∈ Γ → mutez ∈ Γ   →  Formula Γ
  _≥ₘ_    : mutez ∈ Γ → mutez ∈ Γ   →  Formula Γ
  
------------------------- weakening lemmata for abstract execution ----------------------

-- these weakenings are needed since the context may be expanded during any symbolic
-- execution step, but most of the components won't change except for the context
-- they are parameterized by

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

wkφ : ∀ {Γ` Γ} → Formula Γ → Formula (Γ` ++ Γ)
wkφ `false = `false
wkφ (v := trm) = wk∈ v := wk⊢ trm
wkφ (v₁ <ₘ v₂) = wk∈ v₁ <ₘ wk∈ v₂
wkφ (v₁ ≥ₘ v₂) = wk∈ v₁ ≥ₘ wk∈ v₂

φwk : ∀ {Γ` Γ}  → Formula Γ  → Formula (Γ ++ Γ`)
φwk `false = `false
φwk (v := trm) = ∈wk v := ⊢wk trm
φwk (v₁ <ₘ v₂) = ∈wk v₁ <ₘ ∈wk v₂
φwk (v₁ ≥ₘ v₂) = ∈wk v₁ ≥ₘ ∈wk v₂


wkΦ : ∀ {Γ` Γ} → List (Formula Γ) → List (Formula (Γ` ++ Γ))
wkΦ = map wkφ

Φwk : ∀ {Γ` Γ} → List (Formula Γ) → List (Formula (Γ ++ Γ`))
Φwk = map φwk

------------------------- Expanding values of complex Types -----------------------------

-- these functions are needed when symbolically execution PUSH for complex, compound
-- types (that is lists, options, pairs in our Michelson subset)
-- an easy to follow example is provided in the thesis (section 4.3)

-- expandΓ gives all the new variables needed to express any pushable value
-- it will always contain the variable for the pushed value an position 0
-- PJT: the actual value is needed to determine the number of stack locations for options and lists!
expandΓ : Pushable t → ⟦ t ⟧ → Context
expandΓ (base    bt)               x           = [ base bt ]
expandΓ (list   {ty}        P)     []          = [ list ty ]
expandΓ (option {ty}        P)     nothing     = [ option ty ]
expandΓ (option {ty}        P)     (just x)    = [ option ty // expandΓ P  x  ]
expandΓ (pair   {t₁} {t₂} P₁ P₂) (x₁ , x₂)       = [ pair t₁ t₂ // expandΓ P₁ x₁ ++ expandΓ P₂ x₂ ]
expandΓ (list   {ty}        P)     [ x // xs ] = [ list ty // expandΓ P  x  ++ expandΓ (list P) xs ]

-- this is needed to be able to reference the pushed variable for any possible value x
-- during symbolic execution
0∈exΓ : (P : Pushable t) → {x : ⟦ t ⟧} → t ∈ expandΓ P x
0∈exΓ (base bt) = 0∈
0∈exΓ (pair P₁ P₂) = 0∈
0∈exΓ (list P) {[]} = 0∈
0∈exΓ (list P) {[ x // xs ]} = 0∈
0∈exΓ (option P) {just x}  = 0∈
0∈exΓ (option P) {nothing} = 0∈

-- unfold creates all the clauses to be added to express the value x with formulas
-- that only use const terms and the functional terms PAIR, NIL, CONS, SOME, NONE
-- for introduction of compound types
unfold : (P : Pushable t) → (x : ⟦ t ⟧) → List (Formula (expandΓ P x))
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

