
module 14-2-abstract-Exec-state-execution where

open import 01-Types
open import 02-Functions-Interpretations
open import 03-2-concrete-execution
open import 11-abstract-representation-and-weakening
open import 12-2-abstract-execution-accessories-and-weakening 
open import 13-2-abstract-Prog-state-execution

open import Axiom.UniquenessOfIdentityProofs
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import Data.Nat using (ℕ; zero; suc; _+_; _∸_) renaming (_≟_ to _≟ₙ_)
open import Data.List using (List; []; _∷_; _++_; map; concatMap)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; proj₁; proj₂; _,_; -,_ ; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)

open import Data.List.Relation.Unary.All using (All; _∷_; [])
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Membership.Propositional using (_∈_)

open import Function using (_∘_; case_of_)

------------------------- getting Context additions from successor Prog-state -----------

-- when symb. executing αExecState that contains a not yet terminated αProg-state αρ
-- this will again be executed by evaluating αprog-step αρ
-- however this will now yield a disjunction of abstract program states unlike in the
-- concrete setting, and we have to employ ∃⊎Γ++ which proofes for every possible
-- abstract program state that all resulting abstract state disjunctions from αprog-step
-- will be parameterized by an extension of the original context

get⊎Γ : ∀ {ro} → ⊎Prog-state ro → List Context
get⊎Γ ⊎ρ = map proj₁ ⊎ρ

mod⊎wk : List Context → Context → List Context → Set
mod⊎wk []              Γ [] = ⊤
mod⊎wk [ Γ++ // ⊎Γ++ ] Γ [ Γ` // ⊎Γ` ] = Γ++ ++ Γ ≡ Γ` × mod⊎wk ⊎Γ++ Γ ⊎Γ`
mod⊎wk _ _ _ = ⊥

∃⊎Γ++ : ∀ {Γ ro} αρ → ∃[ ⊎Γ++ ] mod⊎wk ⊎Γ++ Γ (get⊎Γ (αprog-step {Γ} {ro} αρ))
∃⊎Γ++ (state αen end r`VM Φ) = [ [] ] , refl , tt
∃⊎Γ++ (state αen (enf `AMOUNT ; prg) r`VM Φ) = [ [] ] , refl , tt
∃⊎Γ++ (state αen (enf `BALANCE ; prg) r`VM Φ) = [ [] ] , refl , tt
∃⊎Γ++ (state αen (enf (`CONTRACT P) ; prg) (adr∈ ∷ r`VM) Φ)
  = [ [ option (contract P) ] ] , refl , tt
∃⊎Γ++ (state αen (fct (D1 {result = result} f) ; prg) r`VM Φ) = [ [ result ] ] , refl , tt
∃⊎Γ++ (state αen (fct (Dm (`UNPAIR {t1} {t2})) ; prg) (p∈ ∷ r`VM) Φ)
  = [ [ t1 / t2 ] ] , refl , tt
∃⊎Γ++ (state αen (fct (Dm `SWAP) ; prg) (x∈ ∷ y∈ ∷ r`VM) Φ) = [ [] ] , refl , tt
∃⊎Γ++ (state αen (fct (Dm `DUP) ; prg) (p∈ ∷ r`VM) Φ) = [ [] ] , refl , tt
∃⊎Γ++ (state αen (fct (`PUSH P x) ; prg) r`VM Φ) = [ expandΓ P x ] , refl , tt
∃⊎Γ++ (state αen (DROP ; prg) (v∈ ∷ r`VM) Φ) = [ [] ] , refl , tt
∃⊎Γ++ (state αen (ITER {ty} x ; prg) (l∈ ∷ r`VM) Φ) = [ [] / [ ty / list ty ] ] , refl , refl , tt
∃⊎Γ++ (state αen (DIP n x ; prg) r`VM Φ) = [ [] ] , refl , tt
∃⊎Γ++ (state αen (IF-NONE {t = t} x x₁ ; prg) (o∈ ∷ r`VM) Φ)
  = [ [] / [ t ] ] , refl , refl , tt
-- ∃⊎Γ++ (state αen (ITER' {ty} x ∙ prg) r`VM (l∈ ∷ s`VM) Φ)
--   = [ [] / [ ty / list ty ] ] , refl , refl , tt
-- ∃⊎Γ++ (state αen (DIP' top ∙ prg) r`VM s`VM Φ) = [ [] ] , refl , tt
-- ∃⊎Γ++ (state αen (`MPUSH front ∙ prg) r`VM s`VM Φ) = [ [] ] , refl , tt
∃⊎Γ++ (state αen (`MPUSH1 x ∙ prg) r`VM Φ) = [ [] ] , refl , tt

------------------------- Execution state execution :D ----------------------------------

open Decidable⇒UIP (_≟_)

dec-∈-≡ : ∀ {Γ} {t} → (x₁ x₂ : t ∈ Γ) → Dec (x₁ ≡ x₂)
dec-∈-≡ (here px) (here px₁) = yes (cong here (≡-irrelevant px px₁))
dec-∈-≡ (here px) (there x₂) = no (λ())
dec-∈-≡ (there x₁) (here px) = no (λ())
dec-∈-≡ (there x₁) (there x₂)
  with dec-∈-≡ x₁ x₂
... | yes p = yes (cong there p)
... | no ¬p = no (λ{ refl → ¬p refl})

find-ctr : ∀ {Γ}{t}{P : Passable t} → List (Formula Γ) → contract P ∈ Γ
  → Maybe Addr
find-ctr [] c∈Γ = nothing
find-ctr ([ `false ]++ rest) c∈Γ = find-ctr rest c∈Γ
find-ctr ([ x <ₘ x₁ ]++ rest) c∈Γ = find-ctr rest c∈Γ
find-ctr ([ x ≥ₘ x₁ ]++ rest) c∈Γ = find-ctr rest c∈Γ
find-ctr {P = P} ([ _:=_ {tx} x x₁ ]++ rest) c∈Γ
  with tx ≟ contract P
... | no _ = find-ctr rest c∈Γ
... | yes refl
  with dec-∈-≡ x c∈Γ
... | no _ = find-ctr rest c∈Γ
find-ctr {P = P} ([ _:=_ x (func x₁ x₂) ]++ rest) c∈Γ | yes refl | yes pp = nothing
find-ctr {P = P} ([ _:=_ x (var x₁) ]++ rest) c∈Γ | yes refl | yes pp = find-ctr rest x₁
find-ctr {P = P} ([ _:=_ x (contr x₁) ]++ rest) c∈Γ | yes refl | yes pp = just x₁

find-tt : ∀ {Γ} → List (Formula Γ) → operation ∈ Γ
  → Maybe (∃[ t ] ∃[ P ] Match Γ (t ∷ mutez ∷ contract {t} P ∷ []))
find-tt [] _ = nothing
find-tt (`false ∷ rest) op∈Γ = find-tt rest op∈Γ
find-tt (_:=_ {t} x rhs ∷ rest) op∈Γ
  with t ≟ operation
... | no _ = find-tt rest op∈Γ
... | yes refl
  with dec-∈-≡ x op∈Γ
... | no _ = find-tt rest op∈Γ
find-tt ([ _:=_ {.ops} x (func (`GEN1 x₁) x₂) ]++ rest) op∈Γ | yes refl | yes refl = nothing
find-tt ([ _:=_ {.ops} x (func (`GEN2 x₁) x₂) ]++ rest) op∈Γ | yes refl | yes refl = nothing
find-tt ([ _:=_ {.ops} x (func `CAR x₂) ]++ rest) op∈Γ | yes refl | yes refl = nothing
find-tt ([ _:=_ {.ops} x (func `CDR x₂) ]++ rest) op∈Γ | yes refl | yes refl = nothing
find-tt ([ _:=_ {.ops} x (func `TRANSFER-TOKENS x₂) ]++ rest) op∈Γ | yes refl | yes refl = just (-, -, x₂)
find-tt (_:=_ {.ops} x (var x₁) ∷ rest) op∈Γ | yes refl | yes refl = find-tt rest x₁
find-tt (x <ₘ x₁ ∷ rest) op∈Γ = find-tt rest op∈Γ
find-tt (x ≥ₘ x₁ ∷ rest) op∈Γ = find-tt rest op∈Γ

find-tt-list : ∀ {Γ}{t} → List (Formula Γ) → list t ∈ Γ
  → Maybe (Match Γ [] ⊎ Match Γ [ t ⨾ list t ])
find-tt-list [] lop∈Γ = nothing
find-tt-list ([ `false ]++ rest) lop∈Γ = find-tt-list rest lop∈Γ
find-tt-list ([ x <ₘ x₁ ]++ rest) lop∈Γ =  find-tt-list rest lop∈Γ
find-tt-list ([ x ≥ₘ x₁ ]++ rest) lop∈Γ =  find-tt-list rest lop∈Γ
find-tt-list {t = t} ([ _:=_ {tx} x rhs ]++ rest) lop∈Γ
  with tx ≟ list t
... | no _ = find-tt-list rest lop∈Γ
... | yes refl
  with dec-∈-≡ x lop∈Γ
... | no _ = find-tt-list rest lop∈Γ
find-tt-list ([ _:=_ x (var x₁) ]++ rest) lop∈Γ | yes refl | yes refl =  find-tt-list rest x₁
find-tt-list ([ _:=_ x (func (`GEN1 x₁) x₂) ]++ rest) lop∈Γ | yes refl | yes refl = nothing
find-tt-list ([ _:=_ x (func (`GEN2 x₁) x₂) ]++ rest) lop∈Γ | yes refl | yes refl = nothing
find-tt-list ([ _:=_ x (func `CAR x₂) ]++ rest) lop∈Γ | yes refl | yes refl = nothing
find-tt-list ([ _:=_ x (func `CDR x₂) ]++ rest) lop∈Γ | yes refl | yes refl = nothing
find-tt-list ([ _:=_ x (func (`NIL _) x₂) ]++ rest) lop∈Γ | yes refl | yes refl = just (inj₁ x₂)
find-tt-list ([ _:=_ x (func `CONS x₂) ]++ rest) lop∈Γ | yes refl | yes refl = just (inj₂ x₂)

-- other than what's mentioned above regarding ∃⊎Γ++ for application of αprog-step,
-- αexec-step is either very similar to exec-step when handling a terminated contract ex.
-- or it unfortunately cannot mimic its behaviour at all when dealing with
-- pending operations. These can only be executed if lots of additional information is
-- present, encoded in elements of Φ, and without assuming such information
-- pending operations cannot be symb. executed and we only to a rather meaningless
-- disjunction since it's all that can be done at this level.
-- the next modules will deal with this shortcoming.
αexec-step : ∀ {Γ} → αExecState Γ → ⊎ExecState

αexec-step {Γ} ασ@(exc αccounts (Fail _) pending) = [ Γ , ασ ]

αexec-step {Γ} (exc
  αccounts
  (Run (pr {ss = s} self sender (state (env _ self-addr send-addr blc∈ amn∈)
                                        end
                                        [ no,ns∈ ]
                                        Φ)))
  pending)
          = [ [ list operation / s // Γ ]
              , exc (βset self-addr (αupdsrg (wkC self) 1∈) (wkβ αccounts))
                     (`INJ₂ [ 0∈ := func `CAR (2+ no,ns∈ ∷ [M])
                           / 1∈ := func `CDR (2+ no,ns∈ ∷ [M]) // wkΦ Φ ])
                     (wkp pending ++ [ 0∈ , self-addr ]) ]
αexec-step {Γ} (exc
  αccounts
  (Run (pr {ss = s} self sender αρ)) pending)
  = build⊎σ (αprog-step αρ) (∃⊎Γ++ αρ)
  where
    build⊎σ : (⊎ρ` : ⊎Prog-state [ pair (list ops) s ])
            → ∃[ ⊎Γ++ ] (mod⊎wk ⊎Γ++ Γ (get⊎Γ ⊎ρ`)) → ⊎ExecState
    build⊎σ [] ([] , tt) = []
    build⊎σ [ Γ` , αρ` // ⊎Γ`,αρ` ] ([ Γ++ // ⊎Γ++ ] , refl , ++Γ≡⊎Γ`)
      = [  Γ` , exc (wkβ αccounts)
                     (Run (pr (wkC self) (wkC sender) αρ`))
                     (wkp pending)
        // build⊎σ ⊎Γ`,αρ` (⊎Γ++ , ++Γ≡⊎Γ`) ]

αexec-step ασ@(exc αccounts (`INJ₂ Φ) []) = [ _ , ασ ]

αexec-step {Γ} ασ@(exc αccounts (`INJ₂ Φ) [ lops∈Γ , send-addr // αpending ])
  with αccounts send-addr
... | nothing = [ Γ , record ασ{ pending = αpending ; MPstate = `AFail Φ } ]
... | just ∃sender@(_ , _ , sender)
  with find-tt-list Φ lops∈Γ
... | nothing = [ Γ , record ασ{ MPstate = `APanic Φ } ]
... | just (inj₁ []) = [ Γ , record ασ{ pending = αpending } ]
... | just (inj₂ [ op∈Γ ⨾ rest∈Γ ])
  with find-tt Φ op∈Γ
... | nothing = [ Γ , record ασ{ MPstate = `APanic Φ } ]
... | just (expected-param-ty , P , [ param∈Γ ⨾ amount∈Γ ⨾ contr∈Γ ])
  with find-ctr Φ contr∈Γ
... | nothing = [ Γ , record ασ{ MPstate = `APanic Φ } ]
... | just self-addr
  with αccounts self-addr
... | nothing = [ Γ , record ασ{ MPstate = `APanic Φ } ]
... | just ∃self@(param-ty , store-ty , self)
  with expected-param-ty ≟ param-ty
... | no _ =  [ Γ , record ασ{ MPstate = `APanic Φ } ]
... | yes refl
  = [ Γ , exc αccounts
              (`AFail (Contract.balance sender <ₘ amount∈Γ ∷ Φ))
              [ rest∈Γ , send-addr // αpending ] ]++
    (case self-addr ≟ₙ send-addr of λ where
    (yes refl) → 
          [ pair param-ty store-ty ∷ Γ
          , exc (wkβ αccounts)
                (Run (pr (wkC self)
                         (wkC sender)
                         (state (env (wkβ αccounts) self-addr send-addr (wk∈ (Contract.balance self))
                                                                        (wk∈ amount∈Γ))
                                (Contract.program self ;∙ end)
                                [ 0∈ ]
                                (0∈ := func `PAIR  [ wk∈ param∈Γ ⨾ wk∈ (Contract.storage self) ] ∷
                                wkΦ (Contract.balance sender ≥ₘ amount∈Γ ∷ Φ)))))
                (wkp [ rest∈Γ , send-addr // αpending ]) ]
    (no _) →
        [ pair param-ty store-ty ∷ mutez ∷ mutez ∷ Γ
        , exc (set send-addr (updblc (wkC sender) 2∈) (wkβ αccounts))
              (Run (pr (updblc (wkC self) 1∈)
                       (updblc (wkC sender) 2∈)
                       (state (env (wkβ αccounts) self-addr send-addr 1∈ (wk∈ amount∈Γ))
                              (Contract.program self ;∙ end)
                              [ 0∈ ]
                              (0∈ := func `PAIR [ wk∈ param∈Γ ⨾ wk∈ (Contract.storage self) ] ∷
                              1∈ := func `ADDm [ wk∈ amount∈Γ ⨾ wk∈ (Contract.balance self) ] ∷
                              2∈ := func (`GEN2 _∸_) [ wk∈ (Contract.balance sender) ⨾ wk∈ amount∈Γ ] ∷
                              wkΦ (Contract.balance sender ≥ₘ amount∈Γ ∷ Φ)))))
              (wkp [ rest∈Γ , send-addr // αpending ]) ])


{-
αexec-step {Γ} ασ@(exc αccounts (inj₂ Φ) [ lops∈Γ , send-addr // pending ])
  with αccounts send-addr
... | nothing = [ Γ , record ασ{ pending = pending } ]
... | just ∃sender@(param-ty , _ , sender)
  = [ Γ , exc αccounts (inj₂ [ lops∈Γ := func (`NIL _) [] // Φ ]) pending
    / [ operation / list operation // Γ ]
    , exc (wkβ αccounts) (inj₂ [ 2+ lops∈Γ := func `CONS (0∈ ∷ 1∈ ∷ [M]) // wkΦ Φ ])
          ( [ 1∈ , send-addr // wkp pending ]) ]
--          (wkp [ lops∈Γ , send-addr // pending ]) ]
-}

-- these are again for convenience ...
⊎exec-step : ⊎ExecState → ⊎ExecState
⊎exec-step states = concatMap (αexec-step ∘ proj₂) states
-- ⊎exec-step [] = []
-- ⊎exec-step [ _ , ασ // ⊎σ ] = αexec-step ασ ++ ⊎exec-step ⊎σ

⊎exec-exec : ℕ → ⊎ExecState → ℕ × ⊎ExecState
⊎exec-exec zero starved = zero , starved
⊎exec-exec gas [] = gas , []
⊎exec-exec gas [ _ , ασ@(exc _ (`INJ₂ _) _) // ⊎σ ] with ⊎exec-exec gas ⊎σ
... | rest , ⊎σ* = rest , [ _ , ασ // ⊎σ* ]
⊎exec-exec (suc gas) ⊎σ = ⊎exec-exec gas (⊎exec-step ⊎σ)

infixl 3 _app-exec_
_app-exec_ : ⊎ExecState → ℕ → ⊎ExecState
⊎σ app-exec gas = proj₂ (⊎exec-exec gas ⊎σ)

