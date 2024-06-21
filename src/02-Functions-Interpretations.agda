
module 02-Functions-Interpretations where

open import 01-Types

open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary

open import Function.Base

open import Data.Bool.Base
open import Data.Nat hiding (_/_)
open import Data.List.Base hiding ([_]; head)
open import Data.List.Relation.Unary.All  
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product
open import Data.Unit

import 00-All-Utilities as H

--! Functions >

-- maybe [_⨾_], [_⨾_⨾_], [_]++_, [_⨾_]++_, [_⨾_⨾_]++_

pattern         [_]       z    =             z ∷ []
pattern       [_/_]     y z    =         y ∷ z ∷ []
pattern     [_/_/_]   x y z    =     x ∷ y ∷ z ∷ []
pattern      [_//_]       z xs =             z ∷ xs
pattern    [_/_//_]     y z xs =         y ∷ z ∷ xs
pattern  [_/_/_//_]   x y z xs =     x ∷ y ∷ z ∷ xs

pattern       [_⨾_]     y z    =         y ∷ z ∷ []
pattern     [_⨾_⨾_]   x y z    =     x ∷ y ∷ z ∷ []
pattern      [_]++_       z xs =             z ∷ xs
pattern    [_⨾_]++_     y z xs =         y ∷ z ∷ xs
pattern  [_⨾_⨾_]++_   x y z xs =     x ∷ y ∷ z ∷ xs

-- onedimensional functions which also constitute most of the `DL terms in a later module
data 1-func : Stack → Type → Set where
  `GEN1    : (⟦ t₁ ⟧ → ⟦ t ⟧)          → 1-func [ t₁ ] t
  `GEN2    : (⟦ t₁ ⟧ → ⟦ t₂ ⟧ → ⟦ t ⟧) → 1-func [ t₁ ⨾ t₂ ] t
  `ADDnn   :       1-func [ nat ⨾ nat ]     nat
  `ADDm    :       1-func [ mutez ⨾ mutez ] mutez
  `CAR     :       1-func [ pair t₁ t₂ ]    t₁
  `CDR     :       1-func [ pair t₁ t₂ ]    t₂
  `PAIR    :       1-func [ t₁ ⨾ t₂ ]       (pair t₁ t₂)
  `NIL     : ∀ t → 1-func []               (list t)
  `NONE    : ∀ t → 1-func []               (option t)
  `SOME    :       1-func [ t ]            (option t)
  `CONS    :       1-func [ t ⨾ list t ]   (list t)
  `SUB-MUTEZ       : 1-func [ mutez ⨾ mutez ] (option mutez)
  `TRANSFER-TOKENS : ∀ {pt : Passable t} → 1-func [ t ⨾  mutez ⨾ contract pt ] ops

-- m-dimensional functions; Stack × Type ensures m ≥ 1
data m-func : Stack → Stack × Type → Set where
  `UNPAIR  : m-func             [ pair t₁ t₂ ]   ([ t₁ ] , t₂)
  `SWAP    : m-func                [ t₁ ⨾ t₂ ]   ([ t₂ ] , t₁)
  `DUP     : m-func                     [ t ]   ([ t ] , t)

-- onedimensional functions for data from the execution environment
-- that will be defined later
data env-func : Stack → Type → Set where
  `AMOUNT    : env-func [] mutez
  `BALANCE   : env-func [] mutez
  `CONTRACT  : (P : Passable t) → env-func  [ addr ]  (option (contract P))

variable
  result : Type
  args : Stack
  results : Stack × Type

-- this type combines all non-environmental function types we implemented
-- `PUSH get's special treatment because its symbolic execution is complicated
data func-type : Stack → Stack × Type → Set where
  D1    : 1-func args result  → func-type args ([] , result)
  Dm    : m-func args results → func-type args       results
  `PUSH  : Pushable t → ⟦ t ⟧  → func-type []   ([] ,     t)

-- a generic way of representing any m-dimensional function implementations
-- of arbitrary arity
⟦_⇒_⟧ : Stack → Stack × Type → Set
⟦       [] ⇒     [] , r ⟧ =                     ⟦ r ⟧
⟦       [] ⇒ x ∷ rl , r ⟧ = ⟦ x ⟧ × ⟦   [] ⇒ rl , r ⟧
⟦ a ∷ args ⇒    results ⟧ = ⟦ a ⟧ → ⟦ args ⇒ results ⟧

-- this Interpretation serves as typed stacks of values in the execution model
-- as well as context interpretations of abstract states of the `DL
-- infixr 5 _∷_
-- data Int : Stack → Set where
--   [I]  : Int []
--   _∷_ : ∀ {t Γ} → ⟦ t ⟧ → Int Γ → Int (t ∷ Γ)

--! Int
Int : Stack → Set
Int = All ⟦_⟧

pattern [I] = []

-- when indexed with any Stack concatenation, these operators allow implicit retrieval
-- of the top and bottom of the Int

Itop : ∀ {top S} → Int (top ++ S) → Int top
Itop = H.top

Ibot : ∀ {top S} → Int (top ++ S) → Int S
Ibot = H.bot

-- same as for lists
takeI : ∀ {S} n → Int S → Int (take n S)
takeI = H.take

dropI : ∀ {S} n → Int S → Int (drop n S)
dropI = H.drop

-- still same as for lists
infixr 10 _+I+_
_+I+_ : ∀ {top S} → Int top → Int S → Int (top ++ S)
_+I+_ = H._++_

sub-mutez : Mutez → Mutez → Maybe Mutez
sub-mutez x y with y ≤? x
... | yes p = just (x ∸ y)
... | no ¬p = nothing

-- this maps all of our function types to their Agda implementation
impl : func-type args results → ⟦ args ⇒ results ⟧
impl (D1 (`GEN1 f))  =  f
impl (D1 (`GEN2 f))  =  f
impl (D1 `ADDnn)     = _+_
impl (D1 `ADDm)      = _+_
impl (D1 `CAR)       = proj₁
impl (D1 `CDR)       = proj₂
impl (D1 `PAIR)      = _,_
impl (D1 (`NIL t))   = []
impl (D1 (`NONE t))  = nothing
impl (D1 `SOME)      = just
impl (D1 `CONS)      = _∷_
impl (Dm `UNPAIR)    = id
impl (Dm `SWAP)      = λ z z₁ → z₁ , z
impl (Dm `DUP)       = λ z → z , z
impl (`PUSH P x)     = x
impl (D1 `SUB-MUTEZ) = sub-mutez
impl (D1 (`TRANSFER-TOKENS {t} {pt})) = transfer-tokens {t} {pt}

-- turning the output type of function types to Stacks = Lists
[×_] : Stack × Type → Stack
[× s , t ] = s ++ t ∷ []

-- generic way of applying argument values to a function that takes these argument types
apply : ∀ {args result} → ⟦ args ⇒ result ⟧ → Int args → Int [× result ]
apply f (x ∷ Iargs) = apply (f x) Iargs
apply {result =           [] , t}       f  [I] = f  ∷ [I]
apply {result = [ tz // lt ] , t} (f₁ , f) [I] = f₁ ∷ apply f [I]

-- to get the singular value from the result of apply when the funtcion is 1D
getvalue : ∀ {t} → Int [ t ] → ⟦ t ⟧
getvalue = head

-- app-fct is a generic way of applying arguments to our functions
-- (represented as their function types)
-- it's definition could be given with only the second line as it originally was,
-- but for the soundness proof it is convenient to define the application of
-- 1D functions separately in the definition of app-fct
appD1 : 1-func args result → Int args → ⟦ result ⟧
appD1 1f Iargs = getvalue (apply (impl (D1 1f)) Iargs)

app-fct : func-type args results → Int args → Int [× results ]
app-fct (D1 1f) Iargs = appD1 1f Iargs ∷ []
app-fct ft Iargs = apply (impl ft) Iargs

------------------------- Instructions and Programs -------------------------------------

infixr 7  _;_
infixr 6  _;;_

-- intrinsically typed Michelson Instructions and Programs
data Instruction : Stack → Stack → Set

Instruction⁺ : Stack → Stack → Set
Instruction⁺ a b = ∀ {s} → Instruction (a ++ s) (b ++ s)

data Program : Stack → Stack → Set where
  end  : Program S S
  _;_  : Instruction  Si   So
       → Program      So   Se
       → Program      Si   Se

-- this gives the implemented subset of Michelson instructions, which are either
-- functional (environmental or not is relevant for the execution model)
-- ore one of the 3 exemplary control flow instructions (instructions that take
-- subprograms as arguments) ... or DROP since it's the only 0D function and easier
-- to just give it its own case than extend func-type for it
data Instruction where
--! Instructionenf
  enf       : env-func args result    → Instruction⁺  args  [ result ]
--! Instructionfct
  fct       : func-type args results  → Instruction⁺  args  [× results ]

  DROP      : Instruction⁺  [ t ]                   []
  ITER      : Program      [         t // S ]                   S
            → Instruction  [ list t // S ]                   S
  DIP       : ∀ n → {T (n ≤ᵇ length S)}
            → Program              (drop n S)                    Se
            → Instruction                  S           (take n S ++ Se)
  IF-NONE   : Program                      S                     Se
            → Program      [         t // S ]                   Se
            → Instruction  [  option t // S ]                   Se

_;;_ : Program Si So → Program So Se → Program Si Se
end     ;; g = g
(i ; p) ;; g = i ; (p ;; g)

pattern GEN1 f           = fct (D1 (`GEN1 f))
pattern GEN2 f           = fct (D1 (`GEN2 f))
pattern ADDnn            = fct (D1 `ADDnn)
pattern ADDm             = fct (D1 `ADDm)
pattern CAR              = fct (D1 `CAR)
pattern CDR              = fct (D1 `CDR)
pattern NIL t            = fct (D1 (`NIL t))
pattern NONE t           = fct (D1 (`NONE t))
pattern SOME             = fct (D1 `SOME)
pattern CONS             = fct (D1 `CONS)
pattern SUB-MUTEZ        = fct (D1 `SUB-MUTEZ)
pattern TRANSFER-TOKENS  = fct (D1 `TRANSFER-TOKENS)
pattern PAIR             = fct (D1 `PAIR)
pattern UNPAIR           = fct (Dm `UNPAIR)
pattern SWAP             = fct (Dm `SWAP)
pattern DUP              = fct (Dm `DUP)
pattern PUSH P t         = fct (`PUSH P t)             
pattern AMOUNT           = enf `AMOUNT
pattern BALANCE          = enf `BALANCE
pattern CONTRACT t       = enf (`CONTRACT t)

example : Program [ pair nat nat ] [ pair (list ops) nat ]
example = UNPAIR ;
          ADDnn ;
          NIL operation ;
          PAIR ;
          end

