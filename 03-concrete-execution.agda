
module 03-concrete-execution where

open import 01-Types
open import 02-Functions-Interpretations

open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary

open import Data.Nat renaming (_≟_ to _≟ₙ_)
open import Data.List.Base hiding ([_])
open import Data.Maybe.Base hiding (map)
open import Data.Product hiding (map)

------------------------- Execution states and program execution ------------------------

record Contract {p s : Type} : Set where
  constructor ctr
  field
    P : Passable p
    S : Storable s
    balance : ⟦ base mutez ⟧
    storage : ⟦ s ⟧
    program : Program [ pair p s ] [ pair (list ops) s ]

update : ∀ {p s} → Contract {p} {s} → ⟦ base mutez ⟧ → ⟦ s ⟧ → Contract {p} {s}
update c blc srg = record c{ balance = blc ; storage = srg }
updsrg : ∀ {p s} → Contract {p} {s} →                  ⟦ s ⟧ → Contract {p} {s}
updsrg c     srg = record c{                 storage = srg }
subamn : ∀ {p s} → Contract {p} {s} → ⟦ base mutez ⟧         → Contract {p} {s}
subamn c amn     = record c{ balance = Contract.balance c ∸ amn }


Blockchain = ⟦ base addr ⟧ → Maybe (∃[ p ] ∃[ s ] Contract {p} {s})

set : ∀ {p s} → ⟦ base addr ⟧ → Contract {p} {s} → Blockchain → Blockchain
set adr c bl a
  with a ≟ₙ adr
... | yes refl = just (_ , _ , c)
... | no  ¬adr = bl a

∅ : Blockchain
∅ adr = nothing

record Environment : Set where
  constructor env
  field
    accounts : Blockchain
    current  : ⟦ base addr ⟧
    sender   : ⟦ base addr ⟧
    balance  : ⟦ base mutez ⟧
    amount   : ⟦ base mutez ⟧

record Prog-state {ro so : Stack} : Set where
  constructor state
  field
    {ri si} : Stack
    en  : Environment
    prg : ShadowProg ri si  ro so
    rSI : Int ri
    sSI : Int si

record Prg-running : Set where
  constructor pr
  field
    {p s x y} : Type
    current : Contract {p} {s}
    sender  : Contract {x} {y}
    ρ       : Prog-state {[ pair (list ops) s ]} {[]}
  
record Exec-state : Set where
  constructor exc
  field
    accounts : Blockchain
    MPstate  : Maybe Prg-running
    pending  : List (List Operation × ⟦ base addr ⟧)

appcontract : ∀ {ty} → (P : Passable ty) → Environment → ⟦ base addr ⟧
         → ⟦ option (contract P) ⟧
appcontract {ty} P en adr
  with Environment.accounts en adr
... | nothing = nothing
... | just (p , s , c)
  with p ≟ ty
... | no  _ = nothing
... | yes _ = just adr

appEF : ∀ {args result} → env-func args result → Environment → Int args → ⟦ result ⟧
appEF AMOUNT  en Iargs = Environment.amount  en
appEF BALANCE en Iargs = Environment.balance en
appEF (CONTRACT {ty} P) en (adr ∷ [I]) = appcontract P en adr

prog-step : ∀ {ro so} → Prog-state {ro} {so} → Prog-state {ro} {so}
prog-step terminal@(state _ end _ _) = terminal
prog-step  ρ@(state _  (fct ft ; prg)   rSI _)
  = record ρ {  prg =            prg  ; rSI = (appft ft    (Itop rSI) +I+ Ibot rSI) }
prog-step  ρ@(state en (enf ef ; prg)   rSI sSI)
  = record ρ {  prg =            prg  ; rSI = (appEF ef en (Itop rSI)   ∷ Ibot rSI) }
prog-step  ρ@(state _    (IF-NONE thn els ; prg)   (nothing ∷ rSI) _)
  = record ρ {  prg =                thn ;∙ prg  ; rSI =      rSI }
prog-step  ρ@(state _    (IF-NONE thn els ; prg)   (just  x ∷ rSI) _)
  = record ρ {  prg =                els ;∙ prg  ; rSI =  x ∷ rSI }
prog-step  ρ@(state _        (ITER     ip ; prg)         (x ∷ rSI)               sSI)
  = record ρ {  prg =         ITER'    ip ∙ prg  ; rSI =      rSI ; sSI =    x ∷ sSI }
prog-step  ρ@(state _        (ITER'    ip ∙ prg)   _                       ([] ∷ sSI))
  = record ρ {  prg =                       prg  ;                  sSI =        sSI }
prog-step  ρ@(state _        (ITER'    ip ∙ prg)              rSI ([ x // xs ] ∷ sSI))
  = record ρ {  prg =   ip ;∙ ITER'    ip ∙ prg  ; rSI =  x ∷ rSI ; sSI = xs   ∷ sSI }
prog-step  ρ@(state {ri} _        (DIP  n   dp ; prg)   rSI sSI)
  = record ρ {  prg =   dp ;∙ DIP' (take n ri) ∙ prg  ; rSI = dropI n rSI
                                                 ; sSI = takeI n rSI +I+ sSI }
prog-step  ρ@(state _        (DIP' top    ∙ prg)   rSI sSI)
  = record ρ {  prg =                       prg  ; rSI = Itop sSI +I+ rSI
                                                 ; sSI = Ibot sSI }
prog-step  ρ@(state _        (DROP        ; prg)    (_ ∷ rSI) _)
  = record ρ {  prg =                       prg  ; rSI = rSI }

exec-step : Exec-state → Exec-state
exec-step σ@(exc
  accounts
  (just (pr current sender (state
    (env _ cadr sadr balance amount) end ((new-ops , new-storage) ∷ [I]) [I])))
  pending)
  with cadr ≟ₙ sadr
... | yes _ = record σ{ accounts = set cadr (updsrg current new-storage) accounts
                      ; MPstate  = nothing
                      ; pending  = pending ++ [ new-ops , cadr ] }
... | no  _ = record σ{ accounts = set cadr (update current balance new-storage)
                                 ( set sadr (subamn sender  amount) accounts)
                      ; MPstate  = nothing
                      ; pending  = pending ++ [ new-ops , cadr ] }
exec-step  σ@(exc _ (just ρr@(pr _ _ ρ)) _)
  = record σ{ MPstate = just (record ρr{ ρ = prog-step ρ }) }
exec-step σ@(exc accounts nothing []) = σ
exec-step σ@(exc accounts nothing [ [] , sadr // pending ])
  = record σ{ pending = pending }
exec-step σ@(exc accounts nothing [ [ transfer-tokens {ty} x tok cadr // more-ops ]
                                  , sadr // pending ])
  with accounts sadr
... | nothing = record σ{ pending = pending }
... | just (p , _ , sender)
  with sadr ≟ₙ cadr
... | yes _
  with ty ≟ p
... | no  _    = record σ{ pending = [ more-ops , sadr // pending ] }
... | yes refl
  = exc accounts
        (just (pr sender sender (state
          (env accounts cadr sadr (Contract.balance sender) zero)
          (Contract.program sender ;∙ end)
          ((x , Contract.storage sender) ∷ [I]) [I])))
        [ more-ops , sadr // pending ]
exec-step σ@(exc accounts nothing [ [ transfer-tokens {ty} x tok cadr // more-ops ]
                                  , sadr // pending ])
    | just (_ , _ , sender) | no _
  with Contract.balance sender <? tok | accounts cadr
... | yes _ | _       = record σ{ pending = [ more-ops , sadr // pending ] }
... | no  _ | nothing = record σ{ pending = [ more-ops , sadr // pending ] }
... | no  _ | just (p , _ , current)
  with ty ≟ p
... | no  _    = record σ{ pending = [ more-ops , sadr // pending ] }
... | yes refl
  = exc accounts
        (just (pr current sender (state
          (env accounts cadr sadr (tok + Contract.balance current) tok)
          (Contract.program current ;∙ end)
          ((x , Contract.storage current) ∷ [I]) [I])))
        [ more-ops , sadr // pending ]

exec-exec : ℕ → Exec-state → ℕ × Exec-state
exec-exec zero starved = zero , starved
exec-exec gas σ@(exc _ nothing []) = gas , σ
exec-exec (suc gas) σ = exec-exec gas (exec-step σ)

