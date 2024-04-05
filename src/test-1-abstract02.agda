
module test-1-abstract02 where

open import 01-Types
open import 02-Functions-Interpretations
-- open import 03-concrete-execution
open import 11-abstract-representation-and-weakening
open import 12-abstract-execution-accessories-and-weakening 
open import 14-abstract-ExecState-execution
open import 15-abstract-special-cases
open import test-1-abstract
open import test-1-abstract01

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

Γ²* = [ base mutez // Γ¹* ]

chain²* : βlockchain Γ²*
chain²* 0 = just (_ , _ , call00      9∈  (10+ 7∈))
chain²* 1 = just (_ , _ , call+1 (10+ 3∈) (10+ 4∈))
chain²* 2 = nothing
chain²* 3 = just (_ , _ , addOne      0∈  (10+ 6∈))
chain²* a = nothing

Φ²* : List (Formula Γ²*)
Φ²* = [         9∈  <ₘ  6∈
      /         0∈  :=  (10+ 5∈) ∸ₘ (10+ 8∈)
      /         1∈  :=  func `PAIR (2∈ ∷ (10+ 7∈) ∷ [M]) //
      [         2∈  :=  func `CONS (4∈ ∷ 3∈ ∷ [M])
      /         3∈  :=  func (`NIL ops) [M]
      /         4∈  :=  func `TRANSFER-TOKENS (5∈ ∷ 6∈ ∷ 7∈ ∷ [M]) //
      [         5∈  :=  const 41
      /         6∈  :=  const 40
      /         7∈  :=  contr 1 //
      [         8∈  :=  func `SOME (7∈ ∷ [M])
      /         9∈  :=  func `ADDm ((10+ 8∈) ∷ (10+ 1∈) ∷ [M])
      /     10+ 0∈  :=  func `PAIR ((10+ 7∈) ∷ (10+ 2∈) ∷ [M]) //
      [     10+ 5∈  ≥ₘ  10+ 8∈
      / 10+ 10+ 0∈  :=  func `TRANSFER-TOKENS ((10+ 7∈) ∷ (10+ 8∈) ∷ (10+ 9∈) ∷ [M])
      /     10+ 7∈  :=  const 1 //
      [     10+ 9∈  :=  contr 0
      / 10+ 10+ 2∈  :=  func `CONS ((10+ 10+ 0∈) ∷ (10+ 10+ 1∈) ∷ [M])
      / 10+ 10+ 1∈  :=  func (`NIL ops) [M] // [ (10+ 4∈) := const 0 ] ] ] ] ] ] ]

Γ³* : Stack
Γ³* = [ contract (base nat) / option (contract (base nat)) / base addr //
      [ base mutez / pair (base nat) (base mutez) // Γ²* ] ]

chain³* : βlockchain Γ³*
chain³* 0 = just (_ , _ , call00 (10+ 4∈) (10+ 10+ 2∈))
chain³* 1 = just (_ , _ , call+1 (10+ 8∈)     (10+ 9∈))
chain³* 2 = nothing
chain³* 3 = just (_ , _ , addOne      5∈  (10+ 10+ 1∈))
chain³* a = nothing

Φ³* : List (Formula Γ³*)
Φ³* = [         0∈  :=  contr 3
      /         1∈  :=  func `SOME (0∈ ∷ [M])
      /         2∈  :=  const 3 //
      [         3∈  :=  func `ADDm ((10+ 1∈) ∷ (10+ 8∈) ∷ [M])
      /         4∈  :=  func `PAIR ((10+ 0∈) ∷ (10+ 9∈) ∷ [M])
      /     10+ 4∈  ≥ₘ  10+ 1∈ //
      [         5∈  :=  (10+ 10+ 0∈) ∸ₘ (10+ 10+ 3∈)
      /         6∈  :=  func `PAIR (7∈ ∷ (10+ 10+ 2∈) ∷ [M])
      /         7∈  :=  func `CONS (9∈ ∷ 8∈ ∷ [M]) //
      [         8∈  :=  func (`NIL ops) [M]
      /         9∈  :=  func `TRANSFER-TOKENS ((10+ 0∈) ∷ (10+ 1∈) ∷ (10+ 2∈) ∷ [M])
      /     10+ 0∈  :=  const 41 //
      [     10+ 1∈  :=  const 40
      /     10+ 2∈  :=  contr 1
      /     10+ 3∈  :=  func `SOME ((10+ 2∈) ∷ [M]) //
      [     10+ 4∈  :=  func `ADDm ((10+ 10+ 3∈) ∷ (10+ 6∈) ∷ [M])
      /     10+ 5∈  :=  func `PAIR ((10+ 10+ 2∈) ∷ (10+ 7∈) ∷ [M])
      / 10+ 10+ 0∈  ≥ₘ  10+ 10+ 3∈ //
      [ 10+ 10+ 5∈  :=  func `TRANSFER-TOKENS
                             ((10+ 10+ 2∈) ∷ (10+ 10+ 3∈) ∷ (10+ 10+ 4∈) ∷ [M])
      / 10+ 10+ 2∈  :=  const 1
      / 10+ 10+ 4∈  :=  contr 0 //
      [ 10+ 10+ 7∈  :=  func `CONS ((10+ 10+ 5∈) ∷ (10+ 10+ 6∈) ∷ [M])
      / 10+ 10+ 6∈  :=  func (`NIL ops) [M]
      /     10+ 9∈  :=  const 0 ] ] ] ] ] ] ] ]
     
s2* : ⊎ExecState
s2* = [ Γ   , αexc chain
                   (inj₂ [ 4∈ <ₘ 7∈ // Φ ]) 
                   []
      / Γ²* , αexc chain²*
                   (inj₂ Φ²*)
                   []
      / Γ³* , αexc chain³*
                   (inj₁ (αpr (call+1 (10+ 8∈)     (10+ 9∈))
                              (call00 (10+ 4∈) (10+ 10+ 2∈))
                              (αstate (αenv chain³* 1 0 3∈ (10+ 1∈))
                                      (fct (D1 `ADDm) ;
                                       `DIP' [ base mutez ] ∙
                                       fct (`PUSH (base mutez) 80) ;
                                       fct (D1 `ADDm) ;
                                       `DIP' [ base nat / contract (base nat) ] ∙
                                       `DIP 1 (fct (Dm `SWAP) ; end) ;
                                       fct (D1 `TRANSFER-TOKENS) ;
                                       fct (D1 (`NIL ops)) ;
                                       fct (Dm `SWAP) ; fct (D1 `CONS) ; fct (D1 `PAIR) ;
                                       end)
                                      ((10+ 1∈) ∷ (10+ 9∈) ∷ [M])
                                      ((10+ 1∈) ∷ (10+ 0∈) ∷ 0∈ ∷ [M])
                                      Φ³*)))
                   [ 8∈ , 0 ]
      ]

s3 = s2* app-ασ-special 2∈ - αρ-spec (app-bf (10+ 2∈ ∷ 10+ 10+ 3∈ ∷ [`MC]))
         app-exec 12

