module test-0-real where

open import 01-Types
import 02-Functions-Interpretations as F
open import 03-1-surface-syntax
open import 03-concrete-execution

open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.List.Membership.Propositional using (_∈_)
open import Relation.Nullary using (yes; no)

open import Data.Nat.Base hiding (_/_)
open import Data.List.Base hiding ([_]) renaming (map to lmap)
open import Data.Maybe.Base
open import Data.Sum hiding ([_,_])
open import Data.Product

------ Test Inputs ----------------------------------------------------------------------

addElems = ctr (list nat) nat 600 0
         (encodeP
         (`CAR
         ; DIP 1 (`PUSH nat 0 ; end)
         ; ITER  (`ADDnn ; end)
         ; `NIL operation
         ; `PAIR
         ; end))

call00 = ctr addr addr 100 0
       (encodeP
       (`CAR ; `DUP ; `CONTRACT nat
       ; IF-NONE
         (`NIL operation ; end)
         (`PUSH mutez 40 ; `PUSH nat 41 ; `TRANSFER-TOKENS
         ; `NIL operation ; `SWAP ; `CONS ; end)
       ; `PAIR
       ; end))

call+1 = ctr nat  mutez 200 0
       (encodeP
       (`UNPAIR
       ; `PUSH addr 3
       ; `CONTRACT nat
       ; IF-NONE
         ( DROP ; `AMOUNT ; `ADDm ; `NIL operation ; end )
         ( `SWAP ; DIP 2
           ( `AMOUNT ; `DUP ; DIP 1 ( `ADDm ; end )
           ; `PUSH mutez 80 ; `ADDm ; end )
         ; DIP 1 ( `SWAP ; end )
         ; `TRANSFER-TOKENS ; `NIL operation
         ; `SWAP ; `CONS ; end )
       ; `PAIR
       ; end))

addOne = ctr nat nat 300 0
       (encodeP
       ( `CAR ; `PUSH nat 1 ; `ADDnn
       ; `NIL operation ; `PAIR
       ; end))

chain = set 0 call00 (set 1 call+1 (set 3 addOne ∅))

init : Blockchain → Operation → ⟦ addr ⟧ → ExecState
init blc op sender = exc blc nothing [ [ op ] , sender ]

show-Prog-state  = λ {ro} {so} ρ
                 → Prog-state.prg {ro} {so} ρ
                 , Prog-state.rSI ρ , Prog-state.s`SI ρ
show-PrgRunning = λ ρr → show-Prog-state (PrgRunning.ρ ρr)
show-exec = λ n σ → proj₂ (exec-exec n σ)
show-`MPexec = λ n σ → ExecState.MPstate (show-exec n σ)
show-act-info = λ (psc : ∃[ p ] ∃[ s ] Contract p s)
              → Contract.balance (proj₂ (proj₂ psc))
              , Contract.storage (proj₂ (proj₂ psc))
show-account = λ n σ a → ExecState.accounts (show-exec n σ) a

  -- terms to normalize:
    -- show-PrgRunning (from-just (show-`MPexec `STEPS `EXSTATE))
    -- ExecState.pending (show-exec `STEPS `EXSTATE)

exc0 = init chain (transfer-tokens {P = addr} 1 50 0) 0

{-

stt = exc chain call00 call00 nothing [ transfer-tokens {P = addr} 1 78 0 , 0 ]



cc : (psc : ∃[ p ] ∃[ s ] Contract p s) → ⟦ mutez ⟧ × ⟦ proj₁ (proj₂ psc) ⟧
cc (p , s , c) = (Contract.balance c) , (Contract.storage c)

Contract→jpsα : ∀ {p} {s} Γ → Contract p s → mutez ∈ Γ → s ∈ Γ
              → Maybe (∃[ p ] ∃[ s ] αContract Γ {p} {s})
Contract→jpsα {p} {s} Γ (ctr P S balance storage program) blc∈ strg∈
  = just (p , s ,       αctr P S blc∈    strg∈   program)

Γ : Context
Γ = [ mutez / addr //
    [ mutez / mutez //
    [ mutez / nat //
    [ nat  / mutez / contract nat //
    [ operation / list operation / list operation ] ] ] ] ]

βc : βlockchain Γ
βc 0 = Contract→jpsα Γ call00 0∈ 1∈
βc 1 = Contract→jpsα Γ call+1 2∈ 3∈
βc 2 = nothing
βc 3 = Contract→jpsα Γ addOne 4∈ 5∈
βc adr = nothing

s0 : ⊎ExecState
s0 = [ _ , αexc βc (inj₂
                [ 9∈     := func (`TRANSFER-TOKENS {pt = nat}) (6∈ ∷ 7∈ ∷ 8∈ ∷ [M])
                / 8∈     := contr 1
                / 10+ 1∈ := func `CONS (9∈ ∷ 10+ 0∈ ∷ [M]) ])
                [ (10+ 1∈) , 0 ] ]

+es = ⊎exec-step

s1 = s0 app-ασ-special 0∈ - new-ops-∃cs 2∈ 0∈ 1∈ refl refl
-- api = αstate (αenv βc 1∈ 1∈ 3∈ 3∈)
-- api = αstate (αenv βc 0 0 3∈ 3∈)
             -- (Contract.program call00 ;∙ end) (0∈ ∷ [M]) [M]
             -- [ 0∈ := func `PAIR (1∈ ∷ 2∈ ∷ [M])
             -- / 1∈ := const 0 ]

+pe = ⊎prog-exec

-- aps : ∀ {ro so} → αProg-state {ro} {so} → Σ Context λ Γ → 
aps : ∀ {Γ ro so} → (αρ : αProg-state Γ {ro} {so})
    → Context × ShadowProg (αProg-state.ri αρ) (αProg-state.si αρ) ro so
    × Match Γ (αProg-state.ri αρ) × Match Γ (αProg-state.si αρ) × List (Formula Γ)
aps {Γ} αρ = Γ , αProg-state.prg αρ , αProg-state.r`VM αρ , αProg-state.s`VM αρ
               , αProg-state.Φ αρ

xxx = λ yy → aps (proj₂ yy)
-- +ps = λ {ro} {so} (⊎ρ : ⊎Prog-state {ro} {so}) → lmap {!aps proj₂!} ⊎ρ
-- +ps = λ (⊎σ : ⊎ExecState) → lmap (proj₂ aps) ⊎σ

+ps : ∀ {ro so} → (⊎ρ : ⊎Prog-state {ro} {so}) → List _
+ps [] = []
+ps [ Γ , αρ // ⊎ρ ] = [ (aps αρ) // +ps ⊎ρ ]

+p1 = [ _ , api ] app-αρ-special 0∈ - `CAR 0∈
+p2 = ⊎prog-step +p1
+p3 =   +p2 app-αρ-special 0∈ - `CTRj 1∈ refl
+p4 =   +p3 app-αρ-special 0∈ - `IF-Nj 0∈

c0-init = init lc 0∈ 7 89

pure-state = λ {ro so} (stt : Prog-state ro so) → Prog-state.prg stt
                                                , Prog-state.rSI stt , Prog-state.s`SI stt

c0i = pure-state c0-init

pp = λ {ro so} ((gas , stt) : ℕ × Prog-state ro so) → gas , (pure-state stt)
c0e = pp (prog-exec 21 c0-init)

ex-init = exc lc [ transfer-tokens {P = addr} 7 89 0 , 42 ] 50
ex = exec-exec 3 ex-init

-- result_call00 = prog-exec 15 (state (env {!!} {!!} {!!}) (shadow call00) ((1 , 0) ∷ [I]) [I])

`BLK = block [ transfer-tokens {addr} 1 89 0 ]
            [ C0 / C1 / C2 ]
            0 0 0 (end {[]} {[]}) [I] [I]

result_call00 = exec 15 `BLK
result_call+1 = exec 22 result_call00
result = exec 5 result_call+1

-- blubb = prog-step (prog-step result)
init-α : ∀ {ri ro} Γ → Abstract-Env Γ → Program ri ro → Match Γ ri → List (Formula Γ)
       → ⊎Boxes
init-α Γ αe prg Mri Φ = [ α→ΣBox (box {αe = αe} (prg ;∙ end) Mri [M] Φ) ]

lookup : ∀ {β} (⊎β : ⊎Boxes) → β ∈ ⊎β → ΣBox
lookup .([ _ // _ ]) (here {β} refl) = β
lookup .([ _ // xs ]) (there {xs = xs} β∈⊎β) = lookup xs β∈⊎β

addIfSome : Program [ pair (option nat) nat ]
                    [ pair (list   operation) nat ]
addIfSome = fct (Dm `UNPAIR)
          ; IF-NONE end (fct (D1 `ADDnn) ; end)
          ; fct  (D1 (`NIL operation))
          ; fct  (D1 `PAIR) ; end
          -- ; fct (D1 

-- blubb = exec-σ  4 (init-σ (env 1 1) addOne ((41 , 1) ∷ [I]))
-- blubb = exec-σ 12 (init-σ (env 1 1) addElems (([ 18 / 24 ] , 0) ∷ [I]))
-- blubb = exec-σ  5 (init-σ (env 1 1) addIfSome ((just 34 , 8) ∷ [I]))
-- blubb = exec-σ  4 (init-σ (env 1 1) addIfSome ((nothing , 8) ∷ [I]))

blubb = init-α [ pair nat nat / mutez / mutez //
               [ nat / nat ] ]
               (αenv 1∈ 2∈) addOne (0∈ ∷ [M])
               [ 0∈ := fct `PAIR (3∈ ∷ 4∈ ∷ [M]) / 3∈ := const 41 ]
        -- appBxS 0∈ app`FOL 0∈ - `CAR-PAIR 1∈ 0∈ app`FOL 0∈ - replace-`VAR 2∈ 0∈
        -- appBxS 0∈ appBxS 0∈ app`FOL 0∈ - app-const-args (1∈ ∷ 2∈ ∷ [`MC]) 0∈
        -- appBxS 0∈ appBxS 0∈
blubb = init-α [ pair (list nat) nat / mutez / mutez ]
               (αenv 1∈ 2∈) addElems (0∈ ∷ [M])
               []
        appBxS 0∈ appBxS 0∈ appBxS 0∈ appBxS 0∈ appBxS 0∈ appBxS 0∈ -- first disjunction
        appBxS 0∈ appBxS 0∈ -- first case end
        appBxS 1∈ appBxS 1∈ appBxS 1∈ appBxS 1∈ -- second disjunction
blubb = init-α [ pair (list nat) nat / mutez / mutez //
               [ list nat / nat / nat //
               [ list nat / nat / list nat ] ] ]
               (αenv 1∈ 2∈) addElems (0∈ ∷ [M])
               [ 0∈ := fct `PAIR (3∈ ∷ 4∈ ∷ [M]) //
               [ 3∈ := fct `CONS (5∈ ∷ 6∈ ∷ [M]) / 5∈ := const 18 //
               [ 6∈ := fct `CONS (7∈ ∷ 8∈ ∷ [M]) / 7∈ := const 24 //
               [ 8∈ := fct (`NIL nat) [M]  ] ] ] ]
        appBxS 0∈
        -- app`FOL 0∈ - `CAR-PAIR 1∈ 0∈ app`FOL 0∈ - replace-`VAR 2∈ 0∈
        appBxS 0∈ appBxS 0∈ appBxS 0∈ appBxS 0∈ appBxS 0∈ -- first disjunction
        app`FOL 0∈ - `CONS-NIL 2∈ 0∈ delBox 0∈ -- invalidate and delete first case
        app`FOL 0∈ - set-args-equal 0∈ 2∈
        app`FOL 0∈ - replace-`VAR 7∈ 0∈ app`FOL 0∈ - replace-`VAR 8∈ 1∈
interm : Abstract-Box [ nat / list nat / nat //
                      [ list nat / pair (list nat) nat / mutez //
                      [ mutez / list nat / nat //
                      [ nat / list nat / nat / list nat ] ] ] ]
                      (stk [ nat / nat ] [ pair (list operation) nat ]
                           [ list nat ] [])
                      (αenv 5∈ 6∈)
interm = box (fct (D1 `ADDnn) ; ITER' (fct (D1 `ADDnn) ; end) ∙ fct (D1 (`NIL operation)) ; fct (D1 `PAIR) ; end)
             (0∈ ∷ 2∈ ∷ [M]) (1∈ ∷ [M])
             [ 0∈ := const 18 / 1∈ := fct `CONS ((10+ 1∈) ∷ (10+ 2∈) ∷ [M]) / 3∈ := fct `CONS (0∈ ∷ 1∈ ∷ [M]) //
             [ 2∈ := const 0 / 3∈ := fct `CONS (9∈ ∷ (10+ 0∈) ∷ [M]) / 4∈ := fct `PAIR (7∈ ∷ 8∈ ∷ [M]) //
             [ 7∈ := fct `CONS (9∈ ∷ (10+ 0∈) ∷ [M]) / 9∈ := const 18 / (10+ 0∈) := fct `CONS ((10+ 1∈) ∷ (10+ 2∈) ∷ [M]) //
             [ (10+ 1∈) := const 24 / (10+ 2∈) := fct (`NIL nat) [M] ] ] ] ]
-- _ : blubb ≡ [ α→ΣBox interm ]
-- _ = refl

blubb = [ α→ΣBox interm ]
        appBxS 0∈ app`FOL 0∈ - app-const-args (1∈ ∷ 4∈ ∷ [`MC]) 0∈
        appBxS 0∈ app`FOL 0∈ - `CONS-NIL 3∈ 0∈ delBox 0∈
        app`FOL 0∈ - set-args-equal 0∈ 3∈
        app`FOL 0∈ - replace-`VAR (10+ 3∈) 0∈ app`FOL 0∈ - replace-`VAR (10+ 4∈) 1∈

interm : Abstract-Box [ nat / list nat / nat //
                      [ nat / list nat / nat //
                      [ list nat / pair (list nat) nat / mutez //
                      [ mutez / list nat / nat //
                      [ nat / list nat / nat / list nat ] ] ] ] ]
                      ( stk [ nat / nat ] [ pair (list operation) nat ]
                            [ list nat ] [] )
                      (αenv 8∈ 9∈)
interm = box (fct (D1 `ADDnn) ; ITER' (fct (D1 `ADDnn) ; end) ∙ fct (D1 (`NIL operation)) ; fct (D1 `PAIR) ; end)
             (0∈ ∷ 2∈ ∷ [M]) (1∈ ∷ [M])
             [ 0∈ := const 24 / 1∈ := fct (`NIL nat) [M] / 4∈ := fct `CONS (0∈ ∷ 1∈ ∷ [M]) //
             [ 2∈ := const 18 / 3∈ := const 18 / 4∈ := fct `CONS ((10+ 4∈) ∷ (10+ 5∈) ∷ [M]) //
             [ 6∈ := fct `CONS (3∈ ∷ 4∈ ∷ [M]) / 5∈ := const 0 / 6∈ := fct `CONS ((10+ 2∈) ∷ (10+ 3∈) ∷ [M]) //
             [ 7∈ := fct `PAIR ((10+ 0∈) ∷ (10+ 1∈) ∷ [M]) / (10+ 0∈) := fct `CONS ((10+ 2∈) ∷ (10+ 3∈) ∷ [M]) / (10+ 2∈) := const 18 //
             [ (10+ 3∈) := fct `CONS ((10+ 4∈) ∷ (10+ 5∈) ∷ [M]) / (10+ 4∈) := const 24 / (10+ 5∈) := fct (`NIL nat) [M] ] ] ] ] ]

blubb = [ α→ΣBox interm ]
        appBxS 0∈ app`FOL 0∈ - app-const-args (1∈ ∷ 4∈ ∷ [`MC]) 0∈
        appBxS 0∈ app`FOL 1∈ - `CONS-NIL 0∈ 3∈ delBox 1∈

Result at this point (only standard end stuff remaining: (fct (D1 (`NIL operation)) ; fct (D1 `PAIR) ; end))
  steps applied:
        appBxS 0∈
          app`FOL 0∈ - `CAR-PAIR 1∈ 0∈
          app`FOL 0∈ - replace-`VAR 2∈ 0∈
        appBxS 0∈
        appBxS 0∈
        appBxS 0∈
        appBxS 0∈
        appBxS 0∈ -- first disjunction
          app`FOL 0∈ - `CONS-NIL 2∈ 0∈
            delBox 0∈ -- invalidate and delete first case
          app`FOL 0∈ - set-args-equal 0∈ 2∈
          app`FOL 0∈ - replace-`VAR 7∈ 0∈
          app`FOL 0∈ - replace-`VAR 8∈ 1∈
        appBxS 0∈
          app`FOL 0∈ - app-const-args (1∈ ∷ 4∈ ∷ [`MC]) 0∈
        appBxS 0∈
          app`FOL 0∈ - `CONS-NIL 3∈ 0∈
            delBox 0∈
          app`FOL 0∈ - set-args-equal 0∈ 3∈
          app`FOL 0∈ - replace-`VAR (10+ 3∈) 0∈
          app`FOL 0∈ - replace-`VAR (10+ 4∈) 1∈
        appBxS 0∈
          app`FOL 0∈ - app-const-args (1∈ ∷ 4∈ ∷ [`MC]) 0∈
        appBxS 0∈
          app`FOL 1∈ - `CONS-NIL 0∈ 3∈
            delBox 1∈
        Total:
          10 BxS / 13 `FOL / 3 del
  Context: 17 vars
       [ nat / nat / list nat //
       [ nat / nat / list nat //
       [ nat / list nat / pair (list nat) nat //
       [ mutez / mutez / list nat //
       [ nat / nat / list nat //
       [ nat / list nat ] ] ] ] ] ]
  17 Formulas
       [ 2∈ := fct (`NIL nat) [M]
       / 0∈ := const 42
       / 1∈ := const 24 //
       [ 2∈ := fct (`NIL nat) [M]
       / 5∈ := fct `CONS (1∈ ∷ 2∈ ∷ [M])
       / 3∈ := const 18 //
       [ 4∈ := const 18
       / 5∈ := fct `CONS ((10+ 5∈) ∷ (10+ 6∈) ∷ [M])
       / 7∈ := fct `CONS (4∈ ∷ 5∈ ∷ [M]) //
       [ 6∈ := const 0
       / 7∈ := fct `CONS ((10+ 3∈) ∷ (10+ 4∈) ∷ [M])
       / 8∈ := fct `PAIR ((10+ 1∈) ∷ (10+ 2∈) ∷ [M]) //
       [ (10+ 1∈) := fct `CONS ((10+ 3∈) ∷ (10+ 4∈) ∷ [M])
       / (10+ 3∈) := const 18
       / (10+ 4∈) := fct `CONS ((10+ 5∈) ∷ (10+ 6∈) ∷ [M]) //
       [ (10+ 5∈) := const 24
       / (10+ 6∈) := fct (`NIL nat) [M] ] ] ] ] ] ]
blubb = init-α [ pair (list nat) nat / mutez / mutez //
               [ list nat / nat / nat //
               [ list nat / nat / list nat ] ] ]
               (αenv 1∈ 2∈) addElems (0∈ ∷ [M])
               [ 0∈ := fct `PAIR (3∈ ∷ 4∈ ∷ [M]) //
               [ 3∈ := fct `CONS (5∈ ∷ 6∈ ∷ [M]) / 5∈ := const 18 //
               [ 6∈ := fct `CONS (7∈ ∷ 8∈ ∷ [M]) / 7∈ := const 24 //
               [ 8∈ := fct (`NIL nat) [M]  ] ] ] ]
        app`SBS 0∈ - `CAR 0∈    appBxS 0∈ appBxS 0∈ appBxS 0∈ appBxS 0∈
        app`SBS 0∈ - ITERxs 2∈ appBxS 0∈ app`FOL 0∈ - app-const-args (4∈ ∷ 1∈ ∷ [`MC]) 0∈
        app`SBS 0∈ - ITERxs 5∈ appBxS 0∈ app`FOL 0∈ - app-const-args (7∈ ∷ 1∈ ∷ [`MC]) 0∈
        app`SBS 0∈ - ITER[] 8∈

  same execution state after:
    10 `BS (4 special ;) / 2 `FOL
  Context: 12 vars
       [ nat / nat / nat //
       [ pair (list nat) nat / mutez / mutez //
       [ list nat / nat / nat //
       [ list nat / nat / list nat ] ] ] ]
  9 (!!!) Formulas: 
       [ 0∈ := const 42
       / 1∈ := const 18
       / 2∈ := const 0 //
       [ 3∈ := fct `PAIR (6∈ ∷ 7∈ ∷ [M])
       / 6∈ := fct `CONS (8∈ ∷ 9∈ ∷ [M])
       / 8∈ := const 18 //
       [ 9∈ := fct `CONS ((10+ 0∈) ∷ (10+ 1∈) ∷ [M])
       / (10+ 0∈) := const 24
       / (10+ 1∈) := fct (`NIL nat) [M] ] ] ]
-}
