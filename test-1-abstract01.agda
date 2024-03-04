
module test-1-abstract01 where

open import 01-Types
open import 02-Functions-Interpretations
-- open import 03-concrete-execution
open import 11-abstract-representation-and-weakening
open import 12-abstract-execution-accessories-and-weakening 
open import 14-abstract-Exec-state-execution
open import 15-abstract-special-cases
open import test-1-abstract

open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.List.Membership.Propositional using (_∈_)
-- open import Relation.Nullary using (yes; no)

open import Data.Fin.Base
open import Data.Nat.Base hiding (_/_)
open import Data.List.Base hiding ([_]) renaming (map to lmap)
open import Data.Maybe.Base
open import Data.Sum hiding ([_,_])
open import Data.Product

------ Test Inputs ----------------------------------------------------------------------

Γ¹* : Stack
Γ¹* = [ pair (list ops) (base addr) / list ops / list ops //
      [ ops / base nat / base mutez //
      [ contract (base nat) / option (contract (base nat)) / base mutez //
      [ pair (base addr) (base addr) // Γ ] ] ] ]

chain¹* : βlockchain Γ¹*
chain¹* 0 = just (_ , _ , call00 (10+ 0∈) (10+ 1∈))
chain¹* 1 = just (_ , _ , call+1 (10+ 2∈) (10+ 3∈))
chain¹* 2 = nothing
chain¹* 3 = just (_ , _ , addOne (10+ 4∈) (10+ 5∈))
chain¹* a = nothing

Φ¹* : List (Formula Γ¹*)
Φ¹* = [         0∈  :=  func PAIR (1∈ ∷ (10+ 6∈) ∷ [M])
      /         1∈  :=  func CONS (3∈ ∷ 2∈ ∷ [M])
      /         2∈  :=  func (NIL ops) [M] //
      [         3∈  :=  func TRANSFER-TOKENS (4∈ ∷ 5∈ ∷ 6∈ ∷ [M])
      /         4∈  :=  const 41
      /         5∈  :=  const 40 //
      [         6∈  :=  contr 1
      /         7∈  :=  func SOME (6∈ ∷ [M])
      /         8∈  :=  func ADDm ((10+ 7∈) ∷ (10+ 0∈) ∷ [M]) //
      [         9∈  :=  func PAIR ((10+ 6∈) ∷ (10+ 1∈) ∷ [M])
      /     10+ 4∈  ≥ₘ  10+ 7∈
      /     10+ 9∈  :=  func TRANSFER-TOKENS ((10+ 6∈) ∷ (10+ 7∈) ∷ (10+ 8∈) ∷ [M]) //
      [     10+ 6∈  :=  const 1
      /     10+ 8∈  :=  contr 0
      / 10+ 10+ 1∈  :=  func CONS ((10+ 9∈) ∷ (10+ 10+ 0∈) ∷ [M]) //
      [ 10+ 10+ 0∈  :=  func (NIL ops) [M]
      /     10+ 3∈  :=  const 0 ] ] ] ] ] ]

s1* : ⊎Exec-state
s1* = [ Γ   , αexc chain
                   (inj₂ [ 4∈ <ₘ 7∈ // Φ ]) 
                   []
      / Γ¹* , αexc chain¹*
                   (inj₁ (αpr (call00 (10+ 0∈) (10+ 1∈)) (addOne (10+ 4∈) (10+ 5∈))
                              (αstate (αenv chain¹* 0 3 8∈ (10+ 7∈))
                                      end (0∈ ∷ [M]) [M]
                                      Φ¹*)))
                   [ (10+ (10+ 0∈)) , 3 ]
      ]

s2 = s1* app-ασ-special 1∈ - αρend 0∈ (λ ())
         app-ασ-special 1∈ - no-NIL (10+ 6∈)
         app-ασ-special 1∈ - no-c≢s 2∈ 4∈ 7∈ refl refl (λ ())
         app-ασ-special 1∈ - no-NIL 4∈
         app-ασ-special 2∈ - αρ-spec (UNPAIR 1∈)
         app-exec 1
         app-ασ-special 2∈ - αρ-spec (CTRjp 0∈ refl)
         app-ασ-special 2∈ - αρ-spec (IF-Ns 1∈)
         app-exec 5

{-
s2 = s1 app-ασ-special {!1∈!} - {!!}
won't refine first hole within 3 minutes

s2 = s1 app-ασ-special 1∈ - αρend 0∈ (λ ())
will lode file within 4 minutes, but can't show Goal within 2 minutes

----------------------------------------------------------------------------------------

+pe = ⊎prog-exec

-- aps : ∀ {ro so} → αProg-state {ro} {so} → Σ Context λ Γ → 
aps : ∀ {Γ ro so} → (αρ : αProg-state Γ {ro} {so})
    → Context × ShadowProg (αProg-state.ri αρ) (αProg-state.si αρ) ro so
    × Match Γ (αProg-state.ri αρ) × Match Γ (αProg-state.si αρ) × List (Formula Γ)
aps {Γ} αρ = Γ , αProg-state.prg αρ , αProg-state.rVM αρ , αProg-state.sVM αρ
               , αProg-state.Φ αρ

xxx = λ yy → aps (proj₂ yy)
-- +ps = λ {ro} {so} (⊎ρ : ⊎Prog-state {ro} {so}) → lmap {!aps proj₂!} ⊎ρ
-- +ps = λ (⊎σ : ⊎Exec-state) → lmap (proj₂ aps) ⊎σ

+ps : ∀ {ro so} → (⊎ρ : ⊎Prog-state {ro} {so}) → List _
+ps [] = []
+ps [ Γ , αρ // ⊎ρ ] = [ (aps αρ) // +ps ⊎ρ ]

+p1 = [ _ , api ] app-αρ-special 0∈ - CAR 0∈
+p2 = ⊎prog-step +p1
+p3 =   +p2 app-αρ-special 0∈ - CTRj 1∈ refl
+p4 =   +p3 app-αρ-special 0∈ - IF-Nj 0∈

c0-init = init lc 0∈ 7 89

pure-state = λ {ro so} (stt : Prog-state ro so) → Prog-state.prg stt
                                                , Prog-state.rSI stt , Prog-state.sSI stt

c0i = pure-state c0-init

pp = λ {ro so} ((gas , stt) : ℕ × Prog-state ro so) → gas , (pure-state stt)
c0e = pp (prog-exec 21 c0-init)

ex-init = exc lc [ transfer-tokens {P = base addr} 7 89 0 , 42 ] 50
ex = exec-exec 3 ex-init

-- result_call00 = prog-exec 15 (state (env {!!} {!!} {!!}) (shadow call00) ((1 , 0) ∷ [I]) [I])

BLK = block [ transfer-tokens {base addr} 1 89 0 ]
            [ C0 / C1 / C2 ]
            0 0 0 (end {[]} {[]}) [I] [I]

result_call00 = exec 15 BLK
result_call+1 = exec 22 result_call00
result = exec 5 result_call+1

-- blubb = prog-step (prog-step result)
init-α : ∀ {ri ro} Γ → Abstract-Env Γ → Program ri ro → Match Γ ri → List (Formula Γ)
       → ⊎Boxes
init-α Γ αe prg Mri Φ = [ α→ΣBox (box {αe = αe} (prg ;∙ end) Mri [M] Φ) ]

lookup : ∀ {β} (⊎β : ⊎Boxes) → β ∈ ⊎β → ΣBox
lookup .([ _ // _ ]) (here {β} refl) = β
lookup .([ _ // xs ]) (there {xs = xs} β∈⊎β) = lookup xs β∈⊎β

addIfSome : Program [ pair (option (base nat)) (base nat) ]
                    [ pair (list   (base ops)) (base nat) ]
addIfSome = fct (Dm UNPAIR)
          ; IF-NONE end (fct (D1 ADDnn) ; end)
          ; fct  (D1 (NIL (base ops)))
          ; fct  (D1 PAIR) ; end
          -- ; fct (D1 

-- blubb = exec-σ  4 (init-σ (env 1 1) addOne ((41 , 1) ∷ [I]))
-- blubb = exec-σ 12 (init-σ (env 1 1) addElems (([ 18 / 24 ] , 0) ∷ [I]))
-- blubb = exec-σ  5 (init-σ (env 1 1) addIfSome ((just 34 , 8) ∷ [I]))
-- blubb = exec-σ  4 (init-σ (env 1 1) addIfSome ((nothing , 8) ∷ [I]))

blubb = init-α [ pair (base nat) (base nat) / base mutez / base mutez //
               [ base nat / base nat ] ]
               (αenv 1∈ 2∈) addOne (0∈ ∷ [M])
               [ 0∈ := fct PAIR (3∈ ∷ 4∈ ∷ [M]) / 3∈ := const 41 ]
        -- appBxS 0∈ appFOL 0∈ - CAR-PAIR 1∈ 0∈ appFOL 0∈ - replace-VAR 2∈ 0∈
        -- appBxS 0∈ appBxS 0∈ appFOL 0∈ - app-const-args (1∈ ∷ 2∈ ∷ [MC]) 0∈
        -- appBxS 0∈ appBxS 0∈
blubb = init-α [ pair (list (base nat)) (base nat) / base mutez / base mutez ]
               (αenv 1∈ 2∈) addElems (0∈ ∷ [M])
               []
        appBxS 0∈ appBxS 0∈ appBxS 0∈ appBxS 0∈ appBxS 0∈ appBxS 0∈ -- first disjunction
        appBxS 0∈ appBxS 0∈ -- first case end
        appBxS 1∈ appBxS 1∈ appBxS 1∈ appBxS 1∈ -- second disjunction
blubb = init-α [ pair (list (base nat)) (base nat) / base mutez / base mutez //
               [ list (base nat) / base nat / base nat //
               [ list (base nat) / base nat / list (base nat) ] ] ]
               (αenv 1∈ 2∈) addElems (0∈ ∷ [M])
               [ 0∈ := fct PAIR (3∈ ∷ 4∈ ∷ [M]) //
               [ 3∈ := fct CONS (5∈ ∷ 6∈ ∷ [M]) / 5∈ := const 18 //
               [ 6∈ := fct CONS (7∈ ∷ 8∈ ∷ [M]) / 7∈ := const 24 //
               [ 8∈ := fct (NIL (base nat)) [M]  ] ] ] ]
        appBxS 0∈
        -- appFOL 0∈ - CAR-PAIR 1∈ 0∈ appFOL 0∈ - replace-VAR 2∈ 0∈
        appBxS 0∈ appBxS 0∈ appBxS 0∈ appBxS 0∈ appBxS 0∈ -- first disjunction
        appFOL 0∈ - CONS-NIL 2∈ 0∈ delBox 0∈ -- invalidate and delete first case
        appFOL 0∈ - set-args-equal 0∈ 2∈
        appFOL 0∈ - replace-VAR 7∈ 0∈ appFOL 0∈ - replace-VAR 8∈ 1∈
interm : Abstract-Box [ base nat / list (base nat) / base nat //
                      [ list (base nat) / pair (list (base nat)) (base nat) / base mutez //
                      [ base mutez / list (base nat) / base nat //
                      [ base nat / list (base nat) / base nat / list (base nat) ] ] ] ]
                      (stk [ base nat / base nat ] [ pair (list (base ops)) (base nat) ]
                           [ list (base nat) ] [])
                      (αenv 5∈ 6∈)
interm = box (fct (D1 ADDnn) ; ITER' (fct (D1 ADDnn) ; end) ∙ fct (D1 (NIL (base ops))) ; fct (D1 PAIR) ; end)
             (0∈ ∷ 2∈ ∷ [M]) (1∈ ∷ [M])
             [ 0∈ := const 18 / 1∈ := fct CONS ((10+ 1∈) ∷ (10+ 2∈) ∷ [M]) / 3∈ := fct CONS (0∈ ∷ 1∈ ∷ [M]) //
             [ 2∈ := const 0 / 3∈ := fct CONS (9∈ ∷ (10+ 0∈) ∷ [M]) / 4∈ := fct PAIR (7∈ ∷ 8∈ ∷ [M]) //
             [ 7∈ := fct CONS (9∈ ∷ (10+ 0∈) ∷ [M]) / 9∈ := const 18 / (10+ 0∈) := fct CONS ((10+ 1∈) ∷ (10+ 2∈) ∷ [M]) //
             [ (10+ 1∈) := const 24 / (10+ 2∈) := fct (NIL (base nat)) [M] ] ] ] ]
-- _ : blubb ≡ [ α→ΣBox interm ]
-- _ = refl

blubb = [ α→ΣBox interm ]
        appBxS 0∈ appFOL 0∈ - app-const-args (1∈ ∷ 4∈ ∷ [MC]) 0∈
        appBxS 0∈ appFOL 0∈ - CONS-NIL 3∈ 0∈ delBox 0∈
        appFOL 0∈ - set-args-equal 0∈ 3∈
        appFOL 0∈ - replace-VAR (10+ 3∈) 0∈ appFOL 0∈ - replace-VAR (10+ 4∈) 1∈

interm : Abstract-Box [ base nat / list (base nat) / base nat //
                      [ base nat / list (base nat) / base nat //
                      [ list (base nat) / pair (list (base nat)) (base nat) / base mutez //
                      [ base mutez / list (base nat) / base nat //
                      [ base nat / list (base nat) / base nat / list (base nat) ] ] ] ] ]
                      ( stk [ base nat / base nat ] [ pair (list (base ops)) (base nat) ]
                            [ list (base nat) ] [] )
                      (αenv 8∈ 9∈)
interm = box (fct (D1 ADDnn) ; ITER' (fct (D1 ADDnn) ; end) ∙ fct (D1 (NIL (base ops))) ; fct (D1 PAIR) ; end)
             (0∈ ∷ 2∈ ∷ [M]) (1∈ ∷ [M])
             [ 0∈ := const 24 / 1∈ := fct (NIL (base nat)) [M] / 4∈ := fct CONS (0∈ ∷ 1∈ ∷ [M]) //
             [ 2∈ := const 18 / 3∈ := const 18 / 4∈ := fct CONS ((10+ 4∈) ∷ (10+ 5∈) ∷ [M]) //
             [ 6∈ := fct CONS (3∈ ∷ 4∈ ∷ [M]) / 5∈ := const 0 / 6∈ := fct CONS ((10+ 2∈) ∷ (10+ 3∈) ∷ [M]) //
             [ 7∈ := fct PAIR ((10+ 0∈) ∷ (10+ 1∈) ∷ [M]) / (10+ 0∈) := fct CONS ((10+ 2∈) ∷ (10+ 3∈) ∷ [M]) / (10+ 2∈) := const 18 //
             [ (10+ 3∈) := fct CONS ((10+ 4∈) ∷ (10+ 5∈) ∷ [M]) / (10+ 4∈) := const 24 / (10+ 5∈) := fct (NIL (base nat)) [M] ] ] ] ] ]

blubb = [ α→ΣBox interm ]
        appBxS 0∈ appFOL 0∈ - app-const-args (1∈ ∷ 4∈ ∷ [MC]) 0∈
        appBxS 0∈ appFOL 1∈ - CONS-NIL 0∈ 3∈ delBox 1∈

Result at this point (only standard end stuff remaining: (fct (D1 (NIL (base ops))) ; fct (D1 PAIR) ; end))
  steps applied:
        appBxS 0∈
          appFOL 0∈ - CAR-PAIR 1∈ 0∈
          appFOL 0∈ - replace-VAR 2∈ 0∈
        appBxS 0∈
        appBxS 0∈
        appBxS 0∈
        appBxS 0∈
        appBxS 0∈ -- first disjunction
          appFOL 0∈ - CONS-NIL 2∈ 0∈
            delBox 0∈ -- invalidate and delete first case
          appFOL 0∈ - set-args-equal 0∈ 2∈
          appFOL 0∈ - replace-VAR 7∈ 0∈
          appFOL 0∈ - replace-VAR 8∈ 1∈
        appBxS 0∈
          appFOL 0∈ - app-const-args (1∈ ∷ 4∈ ∷ [MC]) 0∈
        appBxS 0∈
          appFOL 0∈ - CONS-NIL 3∈ 0∈
            delBox 0∈
          appFOL 0∈ - set-args-equal 0∈ 3∈
          appFOL 0∈ - replace-VAR (10+ 3∈) 0∈
          appFOL 0∈ - replace-VAR (10+ 4∈) 1∈
        appBxS 0∈
          appFOL 0∈ - app-const-args (1∈ ∷ 4∈ ∷ [MC]) 0∈
        appBxS 0∈
          appFOL 1∈ - CONS-NIL 0∈ 3∈
            delBox 1∈
        Total:
          10 BxS / 13 FOL / 3 del
  Context: 17 vars
       [ base nat / base nat / list (base nat) //
       [ base nat / base nat / list (base nat) //
       [ base nat / list (base nat) / pair (list (base nat)) (base nat) //
       [ base mutez / base mutez / list (base nat) //
       [ base nat / base nat / list (base nat) //
       [ base nat / list (base nat) ] ] ] ] ] ]
  17 Formulas
       [ 2∈ := fct (NIL (base nat)) [M]
       / 0∈ := const 42
       / 1∈ := const 24 //
       [ 2∈ := fct (NIL (base nat)) [M]
       / 5∈ := fct CONS (1∈ ∷ 2∈ ∷ [M])
       / 3∈ := const 18 //
       [ 4∈ := const 18
       / 5∈ := fct CONS ((10+ 5∈) ∷ (10+ 6∈) ∷ [M])
       / 7∈ := fct CONS (4∈ ∷ 5∈ ∷ [M]) //
       [ 6∈ := const 0
       / 7∈ := fct CONS ((10+ 3∈) ∷ (10+ 4∈) ∷ [M])
       / 8∈ := fct PAIR ((10+ 1∈) ∷ (10+ 2∈) ∷ [M]) //
       [ (10+ 1∈) := fct CONS ((10+ 3∈) ∷ (10+ 4∈) ∷ [M])
       / (10+ 3∈) := const 18
       / (10+ 4∈) := fct CONS ((10+ 5∈) ∷ (10+ 6∈) ∷ [M]) //
       [ (10+ 5∈) := const 24
       / (10+ 6∈) := fct (NIL (base nat)) [M] ] ] ] ] ] ]
blubb = init-α [ pair (list (base nat)) (base nat) / base mutez / base mutez //
               [ list (base nat) / base nat / base nat //
               [ list (base nat) / base nat / list (base nat) ] ] ]
               (αenv 1∈ 2∈) addElems (0∈ ∷ [M])
               [ 0∈ := fct PAIR (3∈ ∷ 4∈ ∷ [M]) //
               [ 3∈ := fct CONS (5∈ ∷ 6∈ ∷ [M]) / 5∈ := const 18 //
               [ 6∈ := fct CONS (7∈ ∷ 8∈ ∷ [M]) / 7∈ := const 24 //
               [ 8∈ := fct (NIL (base nat)) [M]  ] ] ] ]
        appSBS 0∈ - CAR 0∈    appBxS 0∈ appBxS 0∈ appBxS 0∈ appBxS 0∈
        appSBS 0∈ - ITERxs 2∈ appBxS 0∈ appFOL 0∈ - app-const-args (4∈ ∷ 1∈ ∷ [MC]) 0∈
        appSBS 0∈ - ITERxs 5∈ appBxS 0∈ appFOL 0∈ - app-const-args (7∈ ∷ 1∈ ∷ [MC]) 0∈
        appSBS 0∈ - ITER[] 8∈

  same execution state after:
    10 BS (4 special ;) / 2 FOL
  Context: 12 vars
       [ base nat / base nat / base nat //
       [ pair (list (base nat)) (base nat) / base mutez / base mutez //
       [ list (base nat) / base nat / base nat //
       [ list (base nat) / base nat / list (base nat) ] ] ] ]
  9 (!!!) Formulas: 
       [ 0∈ := const 42
       / 1∈ := const 18
       / 2∈ := const 0 //
       [ 3∈ := fct PAIR (6∈ ∷ 7∈ ∷ [M])
       / 6∈ := fct CONS (8∈ ∷ 9∈ ∷ [M])
       / 8∈ := const 18 //
       [ 9∈ := fct CONS ((10+ 0∈) ∷ (10+ 1∈) ∷ [M])
       / (10+ 0∈) := const 24
       / (10+ 1∈) := fct (NIL (base nat)) [M] ] ] ]
-}
