
module 14-abstract-Exec-state-execution where

open import 01-Types
open import 02-Functions-Interpretations
open import 03-concrete-execution
open import 11-abstract-representation-and-weakening
open import 12-abstract-execution-accessories-and-weakening 
open import 13-abstract-Prog-state-execution 

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality.Core

open import Data.Nat renaming (_≟_ to _≟ₙ_) hiding (_/_)
open import Data.List.Base hiding ([_]; unfold)
open import Data.Maybe.Base hiding (map)
open import Data.Product hiding (map)
open import Data.Sum hiding ([_,_]; map)
open import Data.Unit
open import Data.Empty

open import Data.List.Relation.Unary.Any hiding (map)
open import Data.List.Membership.Propositional using (_∈_)


------------------------- getting Context additions from successor Prog-state -----------

get⊎Γ : ∀ {ro so} → ⊎Prog-state {ro} {so} → List Context
get⊎Γ ⊎ρ = map proj₁ ⊎ρ

mod⊎wk : List Context → Context → List Context → Set
mod⊎wk []              Γ [] = ⊤
mod⊎wk [ Γ++ // ⊎Γ++ ] Γ [ Γ` // ⊎Γ` ] = Γ++ ++ Γ ≡ Γ` × mod⊎wk ⊎Γ++ Γ ⊎Γ`
mod⊎wk _ _ _ = ⊥

∃⊎Γ++ : ∀ {Γ ro so} αρ → ∃[ ⊎Γ++ ] mod⊎wk ⊎Γ++ Γ (get⊎Γ (αprog-step {Γ} {ro} {so} αρ))
∃⊎Γ++ (αstate αen end rVM sVM Φ) = [ [] ] , refl , tt
∃⊎Γ++ (αstate αen (enf AMOUNT ; prg) rVM sVM Φ) = [ [] ] , refl , tt
∃⊎Γ++ (αstate αen (enf BALANCE ; prg) rVM sVM Φ) = [ [] ] , refl , tt
∃⊎Γ++ (αstate αen (enf (CONTRACT P) ; prg) (adr∈ ∷ rVM) sVM Φ)
  = [ [ option (contract P) ] ] , refl , tt
∃⊎Γ++ (αstate αen (fct (D1 {result} f) ; prg) rVM sVM Φ) = [ [ result ] ] , refl , tt
∃⊎Γ++ (αstate αen (fct (Dm (UNPAIR {t1} {t2})) ; prg) (p∈ ∷ rVM) sVM Φ)
  = [ [ t1 / t2 ] ] , refl , tt
∃⊎Γ++ (αstate αen (fct (Dm SWAP) ; prg) (x∈ ∷ y∈ ∷ rVM) sVM Φ) = [ [] ] , refl , tt
∃⊎Γ++ (αstate αen (fct (Dm DUP) ; prg) (p∈ ∷ rVM) sVM Φ) = [ [] ] , refl , tt
∃⊎Γ++ (αstate αen (fct (PUSH P x) ; prg) rVM sVM Φ) = [ expandΓ P x ] , refl , tt
∃⊎Γ++ (αstate αen (DROP ; prg) (v∈ ∷ rVM) sVM Φ) = [ [] ] , refl , tt
∃⊎Γ++ (αstate αen (ITER x ; prg) (l∈ ∷ rVM) sVM Φ) = [ [] ] , refl , tt
∃⊎Γ++ (αstate αen (DIP n x ; prg) rVM sVM Φ) = [ [] ] , refl , tt
∃⊎Γ++ (αstate αen (IF-NONE {ty} x x₁ ; prg) (o∈ ∷ rVM) sVM Φ)
  = [ [] / [ ty ] ] , refl , refl , tt
∃⊎Γ++ (αstate αen (ITER' {ty} x ∙ prg) rVM (l∈ ∷ sVM) Φ)
  = [ [] / [ ty / list ty ] ] , refl , refl , tt
∃⊎Γ++ (αstate αen (DIP' top ∙ prg) rVM sVM Φ) = [ [] ] , refl , tt

------------------------- Execution state execution :D ----------------------------------

αexec-step : ∀ {Γ} → αExec-state Γ → ⊎Exec-state
αexec-step {Γ} (αexc
  αccounts
  (inj₁ (αpr {s = s} current sender (αstate
    (αenv _ cadr sadr blc∈ amn∈) end (no,ns∈ ∷ [M]) [M] Φ))) pending)
  with cadr ≟ₙ sadr
... | yes _ = [ [ list ops / s // Γ ]
              , αexc (βset cadr (αupdsrg (wkC current) 1∈) (wkβ αccounts))
                     (inj₂ [ 0∈ := func CAR (2+ no,ns∈ ∷ [M])
                           / 1∈ := func CDR (2+ no,ns∈ ∷ [M]) // wkΦ Φ ])
                     (wkp pending ++ [ 0∈ , cadr ]) ]
... | no  _ = [ [ list ops / s / base mutez // Γ ]
              , αexc (βset cadr (αupdate (wkC current) (wk∈ blc∈) 1∈)
                     (βset sadr (αupdblc (wkC sender)         2∈) (wkβ αccounts)))
                     (inj₂ [ 0∈ := func CAR (wk∈ no,ns∈ ∷ [M])
                           / 1∈ := func CDR (wk∈ no,ns∈ ∷ [M])
                           / 2∈ := wk⊢ (αContract.balance sender ∸ₘ amn∈) // wkΦ Φ ])
                     (wkp pending ++ [ 0∈ , cadr ]) ]
αexec-step {Γ} (αexc
  αccounts
  (inj₁ (αpr {s = s} current sender αρ)) pending)
  = build⊎σ (αprog-step αρ) (∃⊎Γ++ αρ)
  where
    build⊎σ : (⊎ρ` : ⊎Prog-state {[ pair (list ops) s ]} {[]})
            → ∃[ ⊎Γ++ ] (mod⊎wk ⊎Γ++ Γ (get⊎Γ ⊎ρ`)) → ⊎Exec-state
    build⊎σ [] ([] , tt) = []
    build⊎σ [ Γ` , αρ` // ⊎Γ`,αρ` ] ([ Γ++ // ⊎Γ++ ] , refl , ++Γ≡⊎Γ`)
      = [  Γ` , αexc (wkβ αccounts)
                     (inj₁ (αpr (wkC current) (wkC sender) αρ`))
                     (wkp pending)
        // build⊎σ ⊎Γ`,αρ` (⊎Γ++ , ++Γ≡⊎Γ`) ]
αexec-step ασ@(αexc αccounts (inj₂ Φ) []) = [ _ , ασ ]
αexec-step {Γ} ασ@(αexc αccounts (inj₂ Φ) [ lops∈Γ , adr // pending ])
  with αccounts adr
... | nothing = [ Γ , record ασ{ pending = pending } ]
... | just (p , _ , sender)
  = [ Γ , αexc αccounts (inj₂ [ lops∈Γ := func (NIL _) [M] // Φ ]) pending
    / [ ops / list ops // Γ ]
    , αexc (wkβ αccounts) (inj₂ [ 2+ lops∈Γ := func CONS (0∈ ∷ 1∈ ∷ [M]) // wkΦ Φ ])
           (wkp [ lops∈Γ , adr // pending ]) ]
   {- currently i can also be sure that
      0∈ := func (TRANSFER-TOKENS {ty} {P}) (x∈ ∷ tok∈ ∷ cadr∈ ∷ [M])
      (but just because that's currently the only possibility to get an ops variable)
      but even then:
        -> i can split according to tok∈ ≤ αContract.balance sender
        -> but i CAN'T evaluate αccounts cadr∈ without a given value for cadr∈,
           and splitting on all possible values seems unreasonable
      ~> which is why a general case for initiating the next pending operation 
         doesn't seem reasonable
   -}

⊎exec-step : ⊎Exec-state → ⊎Exec-state
⊎exec-step [] = []
⊎exec-step [ _ , ασ // ⊎σ ] = αexec-step ασ ++ ⊎exec-step ⊎σ

⊎exec-exec : ℕ → ⊎Exec-state → ℕ × ⊎Exec-state
⊎exec-exec zero starved = zero , starved
⊎exec-exec gas [] = gas , []
⊎exec-exec gas [ _ , ασ@(αexc _ (inj₂ _) _) // ⊎σ ] with ⊎exec-exec gas ⊎σ
... | rest , ⊎σ* = rest , [ _ , ασ // ⊎σ* ]
⊎exec-exec (suc gas) ⊎σ = ⊎exec-exec gas (⊎exec-step ⊎σ)

infixl 3 _app-exec_
_app-exec_ : ⊎Exec-state → ℕ → ⊎Exec-state
⊎σ app-exec gas = proj₂ (⊎exec-exec gas ⊎σ)

{-
_⊎exec-exec_ : ⊎Exec-state → ℕ → ℕ × ⊎Exec-state
starved                              ⊎exec-exec zero = zero , starved
[]                                   ⊎exec-exec gas  = gas  , []
[ _ , ασ@(αexc _ (inj₂ _) _) // ⊎σ ] ⊎exec-exec gas  with ⊎σ ⊎exec-exec gas
... | rest , ⊎σ* = rest , [ _ , ασ // ⊎σ* ]
⊎σ ⊎exec-exec (suc gas) = ⊎exec-step ⊎σ ⊎exec-exec gas

infix  09 _∷[]=_
-- _∷[]=_ : ∀ {a b} {B : Set b} {A : B → Set a} {y : B} {x : A y} {xs}
       -- → x ∈ xs → List A → List A
-- x∈ ∷[]= xs` = ?
_∷[]=_ : ∀ {Γ ασ} {⊎σ : ⊎Exec-state} → (Γ , ασ) ∈ ⊎σ → ⊎Exec-state → ⊎Exec-state
here {xs = xs} refl ∷[]= ⊎σ` = ⊎σ` ++ xs
there {x} σ∈ ∷[]= ⊎σ` = [ x // σ∈ ∷[]= ⊎σ` ]

_app-ασ-special_-_ : ∀ {Γ ασ ⊎σ`} ⊎σ → (σ∈ : (Γ , ασ) ∈ ⊎σ) → ασ-special {Γ} ασ ⊎σ`
                   → ⊎Exec-state
_app-ασ-special_-_ {⊎σ` = ⊎σ`} ⊎σ σ∈ sc = σ∈ ∷[]= ⊎σ`
-- _app-ασ-special_-_ {Γ} {⊎σ`} ⊎σ σ∈ sc = σ∈ ∷[]= ⊎σ`

data ασ-special {Γ} : αExec-state Γ → ⊎Exec-state → Set where

αexec-step {Γ} ασ@(αexc αccounts (inj₂ Φ) [ lops∈Γ , adr // pending ])
  with αccounts adr
... | nothing = [ Γ , record ασ{ pending = pending } ]
... | just (p , _ , sender)
  = [ Γ , αexc αccounts (inj₂ [ lops∈Γ := func (NIL _) [M] // Φ ]) pending
    / [ ops / list ops // Γ ]
    , αexc (wkβ αccounts) (inj₂ [ 2+ lops∈Γ := func CONS (0∈ ∷ 1∈ ∷ [M]) // wkΦ Φ ])
           (wkp [ lops∈Γ , adr // pending ]) ]



  where
    init-next : ∀ {Γ} → αExec-state Γ → ⊎Exec-state
    init-next (αexc _ (inj₁ _) _) = []
    init-next ασ@(αexc _ (inj₂ Φ) []) = [ _ , ασ ]
    init-next {Γ} (αexc αccounts (inj₂ Φ) [ lops∈Γ , adr // pending ])
      with αccounts adr
    ... | nothing = init-next (αexc αccounts (inj₂ Φ) pending)
    ... | just (p , _ , sender)
      =  init-next (αexc αccounts (inj₂ [ lops∈Γ := func (NIL _) [M] // Φ ]) pending)
      ++ {!!}
      -- = (init-next {!!} (αexc {[ list ops // Γ ]} (wkβ αccounts) (inj₂ {![ 0∈!}) {!!})) ++ {!!}


    init-next : ∀ {Γ} → List (list ops ∈ Γ × ⟦ base addr ⟧) → αExec-state Γ → ⊎Exec-state
    init-next _ (αexc _ (inj₁ _) _) = []
    init-next [] ασ = [ _ , ασ ]
    init-next {Γ} [ lops∈Γ , adr // pending ] (αexc αccounts (inj₂ Φ) _)
      =  init-next pending (αexc αccounts (inj₂ [ lops∈Γ := func (NIL _) [M] // Φ ]) pending)
      ++ {!!}



αprog-step : ∀ {ro so} → αProg-state {ro} {so} → ⊎Prog-state {ro} {so}
αprog-step terminal@(αstate Γ αen end rVM sVM Φ) = [ terminal ]
αprog-step α@(αstate Γ αen (enf AMOUNT ; prg) rVM sVM Φ)
  = [ record α{ prg = prg ; rVM = αEnvironment.amount αen ∷ rVM } ]
αprog-step α@(αstate Γ αen (enf BALANCE ; prg) rVM sVM Φ)
  = [ record α{ prg = prg ; rVM = αEnvironment.balance αen ∷ rVM } ]
αprog-step (αstate Γ αen (enf (CONTRACT P) ; prg) (adr∈ ∷ rVM) sVM Φ)
  = [ (αstate [ option (contract P) // Γ ] (wkαE αen) prg
              (0∈ ∷ wkM rVM) (wkM sVM) (wkΦ Φ)) ]
αprog-step (αstate Γ αen (fct (D1 {result} f) ; prg) rVM sVM Φ)
  = [ (αstate [ result // Γ ] (wkαE αen) prg
              (0∈ ∷ wkM (Mbot rVM)) (wkM sVM)
              [ 0∈ := wk⊢ (func f (Mtop rVM)) // wkΦ Φ ]) ]
αprog-step (αstate Γ αen (fct (Dm (UNPAIR {t1} {t2})) ; prg) (p∈ ∷ rVM) sVM Φ)
  = [ (αstate [ t1 / t2 // Γ ] (wkαE αen)
              prg (0∈ ∷ 1∈ ∷ wkM rVM) (wkM sVM)
              [ 0∈ := wk⊢ (func CAR (p∈ ∷ [M]))
              / 1∈ := wk⊢ (func CDR (p∈ ∷ [M])) // wkΦ Φ ]) ]
αprog-step α@(αstate Γ αen (fct (Dm SWAP) ; prg) (x∈ ∷ y∈ ∷ rVM) sVM Φ)
  = [ record α{ prg = prg ; rVM = y∈ ∷ x∈ ∷ rVM } ]
αprog-step α@(αstate Γ αen (fct (Dm DUP)  ; prg) (x∈      ∷ rVM) sVM Φ)
  = [ record α{ prg = prg ; rVM = x∈ ∷ x∈ ∷ rVM } ]
αprog-step   (αstate Γ αen (fct (PUSH P x) ; prg) rVM sVM Φ)
  = [ (αstate (expandΓ P x ++ Γ) (wkαE αen) prg
              ((∈wk (0∈exΓ P)) ∷ wkM rVM) (wkM sVM) (Φwk (unfold P x) ++ wkΦ Φ)) ]
αprog-step α@(αstate Γ αen (DROP   ; prg) (v∈ ∷ rVM) sVM Φ)
  = [ record α{ prg = prg ; rVM = rVM } ]
αprog-step α@(αstate Γ αen (ITER x ; prg) (l∈ ∷ rVM) sVM Φ)
  = [ record α{ prg = ITER' x ∙ prg ; rVM = rVM ; sVM = l∈ ∷ sVM } ]
αprog-step α@(αstate Γ αen (DIP top x ; prg) rVM sVM Φ)
  = [ record α{ prg = x ;∙ DIP' top ∙ prg ; rVM = Mbot rVM ; sVM = Mtop rVM +M+ sVM } ]
αprog-step α@(αstate Γ αen (IF-NONE {ty} thn els ; prg) (o∈ ∷ rVM) sVM Φ)
  = [ record α{ prg = thn ;∙ prg ; rVM = rVM ; Φ = [ o∈ := func (NONE ty) [M] // Φ ] }
    / αstate [ ty // Γ ] (wkαE αen) (els ;∙ prg) (0∈ ∷ wkM rVM) (wkM sVM)
             [ there o∈ := func SOME (0∈ ∷ [M]) // wkΦ Φ ] ]
  -- with o∈ := func (NONE ty) [M] φ∈? Φ
-- ... | yes φ∈ = [ record α{ prg = thn ;∙ prg ; rVM = rVM } ]
-- ... | no ¬φ∈
  -- with ∃[ v∈ ] (o∈ := func SOME (v∈ ∷ [M]) φ∈? Φ)
  -- with o∈ := func SOME (_ ∷ [M]) φ∈? Φ
-- ... | WHY!!!!!!!!!!!!!!!!!!! = {!!}
αprog-step α@(αstate Γ αen (ITER' {ty} x ∙ prg) rVM (l∈ ∷ sVM) Φ)
  = [ record α{ prg = prg ; sVM = sVM ; Φ = [ l∈ := func (NIL ty) [M] // Φ ] }
    / αstate [ ty / list ty // Γ ] (wkαE αen) (x ;∙ ITER' x ∙ prg)
             (0∈ ∷ wkM rVM) (1∈ ∷ wkM sVM)
             [ 2+ l∈ := func CONS (0∈ ∷ 1∈ ∷ [M]) // wkΦ Φ ] ]
αprog-step α@(αstate Γ αen (DIP' top ∙ prg) rVM sVM Φ)
  = [ record α{ prg = prg ; rVM = Mtop sVM +M+ rVM ; sVM = Mbot sVM } ]


_appSBS_-_ : ∀ {Γ αe stksᵢ stksₒ α α`}
       → (⊎boxes  : ⊎Boxes)
       → (oldbox∈ : α→ΣBox α  ∈  ⊎boxes)
       → special-case {Γ} {αe} {stksᵢ} {stksₒ} α α`
       → ⊎Boxes
_appSBS_-_ {α` = α`} ⊎b ob∈ sc = ob∈ ∷= (α→ΣBox α`)


data special-case {Γ αe} : ∀ {stksᵢ stksₒ}
     → Abstract-Box Γ stksᵢ αe → Abstract-Box Γ stksₒ αe → Set where


  → TRANSFER-TOKENS is a D1 function
  → ops is no longer a base Type
    ⇒ ops can only exist as terms "func TRANSFER-TOKENS (x∈ ∷ tok∈ ∷ contr∈ ∷ [M])"
    ⇒ init-next can only be executed, when contr∈ is supplied with a value
    → BUT contract P is no base Type (obviously)
      ⇒ just re-introduce it term ...

box-step {stk                ri    _  si _}  (box (func (PUSH ty x) ; prg) rVS sVS Φ)
  = inj₁ ((expandΓ x) , [ ty // ri ] , si , box prg (∈wk 0∈exΓ ∷ wkM rVS) (wkM sVS) (Φwk (unfold x) ++ wkΦ Φ))
box-step {stk       .(args ++ S)   ro si so} (box (func {S = S} (D1func {args} {r} ft) ; prg) rVS sVS Φ)
  = inj₁ ([ r ] , [ r // S ] , si , box prg (0∈ ∷ wkM (Mbot rVS)) (wkM sVS) (0∈ := wk⊢ (func ft (Mtop rVS)) ∷ wkΦ Φ))
box-step {stk .([ pair x r // S ]) ro si so} (box (func {results = ([ x ] ,  r)} {S} (Dmfunc UNPAIR) ; prg) (p∈ ∷ rVS) sVS Φ)
  = inj₁ ([ x / r ] ,  [    x / r // S ] ,   si   , (box prg (0∈ ∷ 1∈ ∷ wkM rVS) (wkM sVS) (0∈ := wk⊢ (func CAR (p∈ ∷ [M])) ∷ 1∈ := wk⊢ (func CDR (p∈ ∷ [M])) ∷ wkΦ Φ)))
box-step {stk .([    r / x // S ]) ro si so} (box (func {results = ([ x ] ,  r)} {S} (Dmfunc SWAP)   ; prg) (r∈ ∷ x∈ ∷ rVS) sVS Φ)
  = inj₁ ([]        ,  [    x / r // S ] ,   si   , (box prg (x∈ ∷ r∈ ∷ rVS) sVS Φ))
box-step {stk .([        x // S ]) ro si so} (box (func {results = ([ x ] , .x)} {S} (Dmfunc DUP)    ; prg) (x∈ ∷ rVS) sVS Φ)
  = inj₁ ([ x ]     ,  [    x / x // S ] ,   si   , (box prg (0∈ ∷ wkM (x∈ ∷ rVS)) (wkM sVS) (0∈ := wk⊢ (var x∈) ∷ wkΦ Φ)))
box-step {stk _ _ si _} {αe = αe} (box (ENV {args} {result} {S} ef ; prg) rVS sVS Φ)
  = inj₁ ([ result ] , [ result // S ] , si , box prg (0∈ ∷ wkM (Mbot rVS)) (wkM sVS) (αappEF ef αe (Mtop rVS) ∷ wkΦ Φ))
box-step                (box (DIP' {top} {rS} {sS} n    ∙ prg)      rVS  sVS  Φ) = inj₁  ([] , top ++ rS , sS , box prg (Mtop sVS +M+ rVS) (Mbot sVS) Φ)
box-step {stk _ _ si _} (box (ITER  {ty} {rS}        ip ; prg) (x ∷ rVS) sVS  Φ) = inj₁  ([] , rS , [ list ty // si ] , box (ITER' ip ∙ prg) rVS (x ∷ sVS) Φ)
box-step {stk _ _ si _} (box (DIP  {top}  {S} n {l≡} dp ; prg)      rVS  sVS  Φ) = inj₁  ([] , S , top ++ si , box (dp ;∙ DIP' n {l≡} ∙ prg) (Mbot rVS) (Mtop rVS +M+ sVS) Φ)
box-step                (box (ITER' {ty} {rS} {sS}   ip ∙ prg) rVS  (x ∷ sVS) Φ) = inj₂ (([] , rS , sS , box prg rVS sVS (x := func (NIL ty) [M] ∷ Φ))
  , ([ ty / list ty ] , [ ty // rS ] , [ list ty // sS ] , box (ip ;∙ ITER' ip ∙ prg) (0∈ ∷ wkM rVS) (1∈ ∷ wkM sVS) (2+ x := func CONS (0∈ ∷ 1∈ ∷ [M]) ∷ wkΦ Φ)) )
box-step {stk _ _ si _} (box (IF-NONE {ty} {S}  thn els ; prg) (x ∷ rVS) sVS  Φ) = inj₂ (([] , S , si , box (thn ;∙ prg) rVS sVS Φ)
  , ([ ty ] , [ ty // S ] , si , box (els ;∙ prg) (0∈ ∷ wkM rVS) (wkM sVS) (there x := func SOME (0∈ ∷ [M]) ∷ wkΦ Φ)))

postulate
  αprog-step : ∀ {ro so} → αProg-state ro so
           → αProg-state ro so ⊎ αProg-state ro so × αProg-state ro so

  what should happen with the new stuff:
    Types:
      address    → ℕ ... can be handled like every other BaseType
      contract P → represented as it's guaranteed address
      ops
    Functions:
      1-func : TRANSFER-TOKENS → creates the tt operation "tt x tok contr"
                               ⇒ abstract func term can represent it in formulas
                                 as a congregated type
      m-func : DUP doesn't need to create new variable! maybe?!?!!!!
      env-func : CONTRACT → turns given address into optional contract Type
    Contract:
      maybe we shouldn't represent it's address as a variable but rather as concrete
        address (everything else is of course a variable, but):
        → then we can implement findAccount/Contract as in the concrete cases

αprog-step terminal@(αstate _ _ end _ _ _) = inj₁ terminal
αprog-step α@(αstate Γ αen (fct (D1 {result} ft) ; prg) rVM sVM Φ) = inj₁
  (αstate [ result // Γ ] (wkαE αen) prg (0∈ ∷ (wkM (Mbot rVM))) (wkM sVM)
    [ (0∈ := wk⊢ (func ft (Mtop rVM))) // wkΦ Φ ])
αprog-step α@(αstate Γ αen (fct (Dm x) ; prg) rVM sVM Φ) = {!!}
αprog-step α@(αstate Γ αen (fct (PUSH x x₁) ; prg) rVM sVM Φ) = {!!}
αprog-step α@(αstate Γ αen (enf ef ; prg) rVM sVM Φ) = {!!}
αprog-step α@(αstate Γ αen (DROP ; prg) rVM sVM Φ) = {!!}
αprog-step α@(αstate Γ αen (ITER x ; prg) rVM sVM Φ) = {!!}
αprog-step α@(αstate Γ αen (DIP top x ; prg) rVM sVM Φ) = {!!}
αprog-step α@(αstate Γ αen (IF-NONE x x₁ ; prg) rVM sVM Φ) = {!!}
αprog-step α@(αstate Γ αen (i ∙ prg) rVM sVM Φ) = {!!}


findαAccount : ∀ {Γ} → (αlc : αBlockchain Γ) → base addr ∈ Γ → Maybe (∃[ αc ] αc ∈ αlc)
findαAccount [] adr∈ = nothing
findαAccount [ αc@(_ , αctr _ _ addr∈ _ _ _) // αlc ] adr∈ = {!!}

αappEF : ∀ {args result Γ} → env-func args result → αEnvironment Γ → Match Γ args
       → Formula [ result // Γ ]
αappEF AMOUNT (αenv _ _ transfrd∈) Margs = {!!}
αappEF ef αe Margs = {!!}
--
αappEF BALANCE (αenv ib∈ tr∈) [M] = 0∈ := wk⊢ (func ADDm (ib∈ ∷ tr∈ ∷ [M]))

private
  variable
    a : Level
    A : Set a

get1 : A ⊎ A × A → A
get1 (inj₁ x) = x
get1 (inj₂ (fst , snd)) = fst
get2 : A ⊎ A × A → A
get2 (inj₁ x) = x
get2 (inj₂ (fst , snd)) = snd

box-step-α₁ = λ {stks Γ αe} α → proj₂ (proj₂ (proj₂ (get1 (box-step {stks} {Γ} {αe} α))))
box-step-α₂ = λ {stks Γ αe} α → proj₂ (proj₂ (proj₂ (get2 (box-step {stks} {Γ} {αe} α))))

------------------------- First Order Logic ---------------------------------------------

data MatchConst {Γ} (Φ : List (Formula Γ)) : Stack → Set where
  [MC]  : MatchConst Φ []
  _∷_ : ∀ {bt S x} {v∈ : base bt ∈ Γ} 
      → (v∈ := const x) ∈ Φ →  MatchConst Φ S → MatchConst Φ [ base bt // S ]

getMatch : ∀ {Γ Φ S} → MatchConst {Γ} Φ S → Match Γ S
getMatch [MC] = [M]
getMatch (_∷_ {v∈ = v∈} x MC) = v∈ ∷ (getMatch MC)

getInt : ∀ {Γ Φ S} → MatchConst {Γ} Φ S → Int S
getInt [MC] = [I]
getInt (_∷_ {x = x} v∈=C MC) = x ∷ (getInt MC)

setM : ∀ {Γ S} → Match Γ S → Match Γ S → List (Formula Γ)
setM [M] [M] = []
setM (v₁∈ ∷ M₁) (v₂∈ ∷ M₂) = v₁∈ := var v₂∈ ∷ setM M₁ M₂

data FOL⇒ {Γ} : Rel (List (Formula Γ)) 0ℓ where
  app-const-args : ∀ {args result v∈ Φ} {d1f : onedim-func args (base result)}
                 → (MCargs : MatchConst {Γ} Φ args)
                 → (redundant : v∈ := func d1f (getMatch MCargs) ∈ Φ)
                 → FOL⇒ Φ (redundant ∷= v∈ := const (appD1 d1f (getInt MCargs)))
  CAR-PAIR       : ∀ {t1 t2} {v1∈ : t1 ∈ Γ} {v2∈ : t2 ∈ Γ} {p∈ v∈ Φ}
                 →               p∈ := func PAIR (v1∈ ∷ v2∈ ∷ [M])  ∈  Φ
                 → (redundant :  v∈ := func CAR         (p∈ ∷ [M])  ∈  Φ)
                 → FOL⇒ Φ (redundant ∷= v∈ := var v1∈)
  CDR-PAIR       : ∀ {t1 t2} {v1∈ : t1 ∈ Γ} {v2∈ : t2 ∈ Γ} {p∈ v∈ Φ}
                 →               p∈ := func PAIR (v1∈ ∷ v2∈ ∷ [M])  ∈  Φ
                 → (redundant :  v∈ := func CDR         (p∈ ∷ [M])  ∈  Φ)
                 → FOL⇒ Φ (redundant ∷= v∈ := var v2∈)
  replace-VAR    : ∀ {ty u∈ v∈ Φ} {trm : Γ ⊢ ty}
                 →               u∈ := trm     ∈  Φ
                 → (redundant :  v∈ := var u∈  ∈  Φ)
                 → FOL⇒ Φ (redundant ∷= v∈ := trm)
  CONS-NIL       : ∀ {ty v∈ x∈ xs∈ Φ}
                 →               v∈ := func CONS (x∈ ∷ xs∈ ∷ [M])  ∈  Φ
                 →               v∈ := func (NIL ty)         [M]   ∈  Φ
                 → FOL⇒ Φ [ `false ]
  SOME-NONE      : ∀ {ty v∈ x∈ Φ}
                 →               v∈ := func SOME (x∈ ∷ [M])  ∈  Φ
                 →               v∈ := func (NONE ty)  [M]   ∈  Φ
                 → FOL⇒ Φ [ `false ]
  set-args-equal : ∀ {args result v∈ Φ} {d1f : onedim-func args result}
                 → {Margs₁ Margs₂ : Match Γ args}
                 →               v∈ := func d1f Margs₁  ∈  Φ
                 →               v∈ := func d1f Margs₂  ∈  Φ
                 → FOL⇒ Φ (setM Margs₁ Margs₂ ++ Φ)

------------------------- special cases for box transitions -----------------------------

data special-case {Γ αe} : ∀ {stksᵢ stksₒ}
     → Abstract-Box Γ stksᵢ αe → Abstract-Box Γ stksₒ αe → Set where
  CAR    : ∀ {ty₁ ty₂ S ro si so p∈ v₁∈ v₂∈ Φ prg rVM sVM}
         → p∈ := func (PAIR {ty₁} {ty₂}) (v₁∈ ∷ v₂∈ ∷ [M])  ∈  Φ
         → special-case {stksᵢ = stk [ pair ty₁ ty₂ // S ] ro si so}
                        (box (func (D1func CAR) ; prg)  (p∈ ∷ rVM) sVM Φ)
                        (box                      prg  (v₁∈ ∷ rVM) sVM Φ)
  CDR    : ∀ {ty₁ ty₂ S ro si so p∈ v₁∈ v₂∈ Φ prg rVM sVM}
         → p∈ := func (PAIR {ty₁} {ty₂}) (v₁∈ ∷ v₂∈ ∷ [M])  ∈  Φ
         → special-case {stksᵢ = stk [ pair ty₁ ty₂ // S ] ro si so}
                        (box (func (D1func CDR) ; prg)  (p∈ ∷ rVM) sVM Φ)
                        (box                      prg  (v₂∈ ∷ rVM) sVM Φ)
  ITERxs : ∀ {ty sS ri ro so l∈ x∈ xs∈ Φ ip prg rVM sVM}
         → l∈ := func (CONS {ty}) (x∈ ∷ xs∈ ∷ [M])  ∈  Φ
         → special-case {stksᵢ = stk ri ro [ list ty // sS ] so}
                        (box       (ITER' ip ∙ prg)       rVM   (l∈ ∷ sVM) Φ)
                        (box (ip ;∙ ITER' ip ∙ prg) (x∈ ∷ rVM) (xs∈ ∷ sVM) Φ)
  ITER[] : ∀ {ty sS ri ro so l∈ Φ ip prg rVM sVM}
         → l∈ := func (NIL ty) [M]  ∈  Φ
         → special-case {stksᵢ = stk ri ro [ list ty // sS ] so}
                        (box       (ITER' ip ∙ prg)       rVM   (l∈ ∷ sVM) Φ)
                        (box                   prg        rVM         sVM  Φ)
  IF-Nn  : ∀ {ty S Se ro si so o∈ Φ thn els prg rVM sVM}
         → o∈ := func (NONE ty) [M]  ∈  Φ
         → special-case {stksᵢ = stk [ option ty // S ] ro si so}
                        (box (IF-NONE {Se = Se} thn els ;  prg) (o∈ ∷ rVM) sVM Φ)
                        (box                   (thn     ;∙ prg)       rVM  sVM Φ)
  IF-Nj  : ∀ {ty S Se ro si so o∈ x∈ Φ thn els prg rVM sVM}
         → o∈ := func (SOME {ty}) (x∈ ∷ [M])  ∈  Φ
         → special-case {stksᵢ = stk [ option ty // S ] ro si so}
                        (box (IF-NONE {Se = Se} thn els ;  prg) (o∈ ∷ rVM) sVM Φ)
                        (box                       (els ;∙ prg) (x∈ ∷ rVM) sVM Φ)

------------------------- box disjunction and step application --------------------------

ΣBox = Σ Context λ Γ → Σ Stacks λ stks → Σ (Abstract-Env Γ) λ αe → Abstract-Box Γ stks αe

⊎Boxes = List ΣBox

α→ΣBox : ∀ {Γ stks αe} → Abstract-Box Γ stks αe → ΣBox
α→ΣBox {Γ} {stks} {αe} α = Γ , stks , αe , α

ΣBox→α : (β : ΣBox) → Abstract-Box (proj₁ β) (proj₁ (proj₂ β)) (proj₁ (proj₂ (proj₂ β)))
ΣBox→α β = proj₂ (proj₂ (proj₂ β))

infixl 3 _appBxS_ 
infixl 3 _appFOL_-_
infixl 3 _appSBS_-_
infixl 3 _delBox_

_appBxS_ : ∀ {Γ stks αe} {α : Abstract-Box Γ stks αe}
       → (⊎boxes  : ⊎Boxes)
       → (oldbox∈ : α→ΣBox α  ∈  ⊎boxes)
       → ⊎Boxes
_appBxS_ {α = α} ⊎b ob∈ with box-step α
... | inj₁   (_ , _ , _ , α`)   = ob∈ ∷= (α→ΣBox α`)
... | inj₂ ( (_ , _ , _ , α`)
           , (_ , _ , _ , α‶) ) = ob∈ ∷= (α→ΣBox α`) / (α→ΣBox α‶)

_appFOL_-_ : ∀ {Γ stks αe prg rVM sVM Φ Φ`}
       → (⊎boxes  : ⊎Boxes)
       → (oldbox∈ : α→ΣBox (box {Γ} {stks} {αe} prg rVM sVM Φ)  ∈  ⊎boxes)
       → FOL⇒ Φ Φ`
       → ⊎Boxes
_appFOL_-_ {αe = αe} {prg} {rVM} {sVM} {Φ` = Φ`} ⊎b ob∈ fol⇒
  = ob∈ ∷= (α→ΣBox (box {αe = αe} prg rVM sVM Φ`))

_appSBS_-_ : ∀ {Γ αe stksᵢ stksₒ α α`}
       → (⊎boxes  : ⊎Boxes)
       → (oldbox∈ : α→ΣBox α  ∈  ⊎boxes)
       → special-case {Γ} {αe} {stksᵢ} {stksₒ} α α`
       → ⊎Boxes
_appSBS_-_ {α` = α`} ⊎b ob∈ sc = ob∈ ∷= (α→ΣBox α`)

_delBox_ : ∀ {Γ stks αe prg rVM sVM}
       → (⊎boxes  : ⊎Boxes)
       → (badbox∈ : α→ΣBox(box {Γ} {stks} {αe} prg rVM sVM [ `false ])  ∈  ⊎boxes)
       → ⊎Boxes
⊎b delBox bb∈ = del bb∈

-}

