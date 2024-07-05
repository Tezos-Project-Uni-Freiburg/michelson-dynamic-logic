
module 11-1-examples where

open import 01-Types
open import 02-Functions-Interpretations
open import 03-2-concrete-execution
open import 11-abstract-representation-and-weakening

open import Level
open import Relation.Binary.PropositionalEquality hiding ([_])

open import Data.Unit using (tt; ⊤)
open import Data.Nat hiding (_/_)
open import Data.List using (List; []; _∷_; map; _++_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)

open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Membership.Propositional


--! Examples >

module example-0 where

--! Int
  a-stack : Int (nat ∷ unit ∷ option addr ∷ [])
  a-stack =  42 ∷ tt ∷ nothing ∷ []

module example-1 where
  Γ₁ : Context
--!! Context
  Γ₁ = nat ∷ nat ∷ nat ∷ []

  x : nat ∈ Γ₁
--!! XZero
  x = 0∈

  y : nat ∈ Γ₁
  y = 1∈

  v : nat ∈ Γ₁
  v = 2∈

--! AStack
  a-stack : Match Γ₁ (nat ∷ [])
  a-stack = [ x ]
  

--! EqnPlus
  x=y+3  : List (Formula Γ₁)
  x=y+3  = x := func `ADDnn (y ∷ v ∷ [])
         ∷ v := const 3
         ∷ []

module example-2 where
  Γ₂ : Context
--!! ContextList
  Γ₂ = list nat ∷ list nat ∷ list nat ∷ nat ∷ nat ∷ []

  c₁ : list nat ∈ Γ₂
  c₁ = 0∈

  c₂ : list nat ∈ Γ₂
  c₂ = 1∈

  c₃ : list nat ∈ Γ₂
  c₃ = 2∈

  x₀ : nat ∈ Γ₂
  x₀ = 3∈

  x₁ : nat ∈ Γ₂
  x₁ = 4∈

--! EqnList
  eqn  : List (Formula Γ₂)
  eqn  = c₁ := func `CONS (x₀ ∷ c₂ ∷ [])
       ∷ c₂ := func `CONS (x₁ ∷ c₃ ∷ [])
       ∷ c₃ := func (`NIL nat) []
       ∷ x₀ := const 0
       ∷ x₁ := const 1
       ∷ []

