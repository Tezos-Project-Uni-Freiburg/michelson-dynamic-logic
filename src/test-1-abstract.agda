
module test-1-abstract where

open import 01-Types
open import 02-Functions-Interpretations
open import 11-abstract-representation-and-weakening
open import 12-abstract-execution-accessories-and-weakening 
open import 14-abstract-ExecState-execution
open import 15-abstract-special-cases

open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.List.Membership.Propositional using (_∈_)

open import Data.Nat.Base hiding (_/_)
open import Data.List.Base hiding ([_]) renaming (map to lmap)
open import Data.Maybe.Base
open import Data.Sum hiding ([_,_])
open import Data.Product

------ Test Inputs ----------------------------------------------------------------------

call00 = λ {Γ : Context} (blc∈ : base mutez ∈ Γ) (srg∈ : base addr ∈ Γ)
       → αctr {Γ} (base addr) (base addr) blc∈ srg∈
       ( fct (D1 `CAR) ; fct (Dm `DUP) ; enf (`CONTRACT (base nat))
       ; `IF-NONE ( fct (D1 (`NIL ops)) ; end )
         ( fct (`PUSH (base mutez) 40) ; fct (`PUSH (base nat) 41)
         ; fct (D1 `TRANSFER-TOKENS)
         ; fct (D1 (`NIL ops)) ; fct (Dm `SWAP) ; fct (D1 `CONS) ; end )
       ; fct (D1 `PAIR)
       ; end)

call+1 = λ {Γ : Context} (blc∈ : base mutez ∈ Γ) (srg∈ : base mutez ∈ Γ)
       → αctr {Γ} (base nat)  (base mutez) blc∈ srg∈
       ( fct (Dm `UNPAIR)
       ; fct (`PUSH (base addr) 3) ; enf (`CONTRACT (base nat))
       ; `IF-NONE
         ( `DROP ; enf `AMOUNT ; fct (D1 `ADDm) ; fct (D1 (`NIL ops)) ; end )
         ( fct (Dm `SWAP) ; `DIP 2
           ( enf `AMOUNT ; fct (Dm `DUP) ; `DIP 1 ( fct (D1 `ADDm) ; end )
           ; fct (`PUSH (base mutez) 80) ; fct (D1 `ADDm) ; end )
         ; `DIP 1 ( fct (Dm `SWAP) ; end )
         ; fct (D1 `TRANSFER-TOKENS) ; fct (D1 (`NIL ops))
         ; fct (Dm `SWAP) ; fct (D1 `CONS) ; end )
       ; fct (D1 `PAIR)
       ; end)

addOne = λ {Γ : Context} (blc∈ : base mutez ∈ Γ) (srg∈ : base nat ∈ Γ)
       → αctr {Γ} (base nat)  (base nat) blc∈ srg∈
       ( fct (D1 `CAR) ; fct (`PUSH (base nat) 1) ; fct (D1 `ADDnn)
       ; fct (D1 (`NIL ops)) ; fct (D1 `PAIR)
       ; end)

Γ : Context
Γ = [ base mutez / base addr //
    [ base mutez / base mutez //
    [ base mutez / base nat //
    [ base addr  / base mutez / contract (base addr) //
    [ ops / list ops / list ops ] ] ] ] ]

chain : βlockchain Γ
chain 0 = just (_ , _ , call00 0∈ 1∈)
chain 1 = just (_ , _ , call+1 2∈ 3∈)
chain 2 = nothing
chain 3 = just (_ , _ , addOne 4∈ 5∈)
chain a = nothing

Φ : List (Formula Γ)
Φ = [     9∈  :=  func `TRANSFER-TOKENS (6∈ ∷ 7∈ ∷ 8∈ ∷ [])
    /     6∈  :=  const 1
    /     8∈  :=  contr 0 //
    [ 10+ 1∈  :=  func `CONS (9∈ ∷ 10+ 0∈ ∷ [])
    / 10+ 0∈  :=  func (`NIL _) []
    /     3∈  :=  const 0 ] ]

s0 : ⊎ExecState
s0 = [ Γ , αexc chain
                (inj₂ Φ)
                [ (10+ 1∈) , 3 ] ]

s1 = s0 app-ασ-special 0∈ - no-c≢s 3∈ 0∈ 2∈ refl refl (λ ())
        app-ασ-special 0∈ - no-`NIL 5∈
        app-ασ-special 1∈ - αρ-spec (`CAR 1∈)
        app-exec 1
        app-ασ-special 1∈ - αρ-spec (`CTRjp 4∈ refl)
        app-ασ-special 1∈ - αρ-spec (`IF-Ns 1∈)
        app-exec 7

        -- app-ασ-special 1∈ - ?
        -- even with new chain this takes >1min ...

