
module 27-special-execstep-soundness where

open import 01-Types
open import 02-Functions-Interpretations
open import 03-concrete-execution
open import 11-abstract-representation-and-weakening
open import 12-abstract-execution-accessories-and-weakening
open import 13-abstract-Prog-state-execution
open import 15-abstract-special-cases
open import 21-Prog-state-modeling
open import 22-P-s-m-weakening
open import 24-Exec-state-modeling
open import 26-special-progstep-soundness renaming (soundness to ρsp-sound)

open import Relation.Binary.PropositionalEquality.Core

open import Data.Nat renaming (_≟_ to _≟ₙ_) hiding (_/_)
open import Data.List.Base hiding ([_])
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product
open import Data.Sum

open import Data.List.Relation.Unary.All using (All; _∷_; [])
open import Data.List.Relation.Unary.Any
open import Data.List.Membership.Propositional using (_∈_)

open import Relation.Nullary
open import Data.Empty
open import Data.Nat.Properties using (≮⇒≥)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product.Properties using (,-injectiveˡ)

open import Data.Unit using (⊤; tt)


soundness : ∀ {Γ γ ασ ⊎σ`}
          → ασ-special ασ ⊎σ`
          → (σ : ExecState)
          → modσ {Γ} γ ασ σ
          → ∃[ Γ` ] ∃[ γ` ] mod⊎σ {Γ` ++ Γ} (γ` +I+ γ) ⊎σ` (exec-step σ)

soundness (αρendc=s newos=`PAIR)
  (exc accounts (just (pr current sender (state (env acts curr curr balance amount)
                                                .end (_ ∷ [I]) [I]))) pending)
  ( mβ , (refl , refl , refl , refl , (refl , refl , refl , refl , refl) , ms
  , refl , refl , (mβ' , refl , refl , refl , refl) , refl , (refl , tt) , tt , mΦ) , mp)
  with curr ≟ₙ curr
... | no  c≢c  = ⊥-elim (c≢c refl)
... | yes refl
  with modφ∈Φ newos=`PAIR mΦ
... | nos≡no,ns rewrite nos≡no,ns = [] , [I] , _ , 0∈
  , modset curr (refl , refl , refl , refl , refl) mβ , mΦ , mp +modp+ refl , refl

soundness (αρend newos=`PAIR cadr≢sadr) 
  (exc accounts (just (pr current sender (state (env acts curr send balance amount)
                                                .end (_ ∷ [I]) [I]))) pending)
  ( mβ , (refl , refl , refl , refl
  , (refl , refl , refl , refl , refl)
  , (refl , refl , refl , refl , refl)
  , refl , refl , (mβ' , refl , refl , refl , refl) , refl , (refl , tt) , tt , mΦ) , mp)
  with curr ≟ₙ send
... | yes refl = ⊥-elim (cadr≢sadr refl)
... | no  c≢s
  with modφ∈Φ newos=`PAIR mΦ
... | nos≡no,ns rewrite nos≡no,ns = [ mutez ]
  , ((Contract.balance sender ∸ amount) ∷ [I]) , _ , 0∈
  , modset curr (refl , refl , refl , refl , refl)
   (modset send (refl , refl , refl , refl , refl) (wkmodβ mβ))
  , (refl , wkmodΦ mΦ) , wkmodp mp +modp+ refl , refl

soundness (αρ-spec ρsp@(`CAR x))
  (exc accounts (just (pr current sender
                          ρ@(state en (fct (D1 `CAR) ; prg) (p ∷ rSI) s`SI))) pending)
  ( mβ , (refl , refl , refl , refl , mc , ms
  , mρ@(refl , refl , mE , refl , (refl , mrS) , msS , mΦ)) , mp)
  with ρsp-sound ρsp ρ mρ
... | [I] , mρ` = [] , [I] , _ , 0∈
  , (wkmodβ mβ , (refl , refl , refl , refl , mc , ms , mρ`) , wkmodp mp)

soundness (αρ-spec ρsp@(`CDR x))
  (exc accounts (just (pr current sender
                          ρ@(state en (fct (D1 `CDR) ; prg) (p ∷ rSI) s`SI))) pending)
  ( mβ , (refl , refl , refl , refl , mc , ms
  , mρ@(refl , refl , mE , refl , (refl , mrS) , msS , mΦ)) , mp)
  with ρsp-sound ρsp ρ mρ
... | [I] , mρ` = [] , [I] , _ , 0∈
  , (wkmodβ mβ , (refl , refl , refl , refl , mc , ms , mρ`) , wkmodp mp)

soundness (αρ-spec ρsp@(`UNPAIR x))
  (exc accounts (just (pr current sender
                          ρ@(state en (fct (Dm `UNPAIR) ; prg) (p ∷ rSI) s`SI))) pending)
  ( mβ , (refl , refl , refl , refl , mc , ms
  , mρ@(refl , refl , mE , refl , (refl , mrS) , msS , mΦ)) , mp)
  with ρsp-sound ρsp ρ mρ
... | [I] , mρ` = [] , [I] , _ , 0∈
  , (wkmodβ mβ , (refl , refl , refl , refl , mc , ms , mρ`) , wkmodp mp)

soundness (αρ-spec {Γ` = Γ`} ρsp@(`CTRn x x₁))
  (exc accounts (just (pr current sender
                          ρ@(state en (enf (`CONTRACT P) ; prg) (a ∷ rSI) s`SI))) pending)
  ( mβ , (refl , refl , refl , refl , mc , ms
  , mρ@(refl , refl , mE , refl , (refl , mrS) , msS , mΦ)) , mp)
  with ρsp-sound ρsp ρ mρ
... | γ` , mρ` = Γ` , γ` , _ , 0∈
  , wkmodβ mβ , (refl , refl , refl , refl , wkmodC {γ` = γ`} mc , wkmodC {γ` = γ`} ms
              , mρ`) , wkmodp mp

soundness (αρ-spec {Γ` = Γ`} ρsp@(`CTR¬p x x₁ x₂))
  (exc accounts (just (pr current sender
                          ρ@(state en (enf (`CONTRACT P) ; prg) (a ∷ rSI) s`SI))) pending)
  ( mβ , (refl , refl , refl , refl , mc , ms
  , mρ@(refl , refl , mE , refl , (refl , mrS) , msS , mΦ)) , mp)
  with ρsp-sound ρsp ρ mρ
... | γ` , mρ` = Γ` , γ` , _ , 0∈
  , wkmodβ mβ , (refl , refl , refl , refl , wkmodC {γ` = γ`} mc , wkmodC {γ` = γ`} ms
              , mρ`) , wkmodp mp

soundness (αρ-spec {Γ` = Γ`} ρsp@(`CTRjp x x₁))
  (exc accounts (just (pr current sender
                          ρ@(state en (enf (`CONTRACT P) ; prg) (a ∷ rSI) s`SI))) pending)
  ( mβ , (refl , refl , refl , refl , mc , ms
  , mρ@(refl , refl , mE , refl , (refl , mrS) , msS , mΦ)) , mp)
  with ρsp-sound ρsp ρ mρ
... | γ` , mρ` = Γ` , γ` , _ , 0∈
  , wkmodβ mβ , (refl , refl , refl , refl , wkmodC {γ` = γ`} mc , wkmodC {γ` = γ`} ms
              , mρ`) , wkmodp mp

soundness (αρ-spec ρsp@(`IF-Nn x))
  (exc accounts (just (pr current sender
                          ρ@(state en (IF-NONE thn els ; prg) (o ∷ rSI) s`SI))) pending)
  ( mβ , (refl , refl , refl , refl , mc , ms
  , mρ@(refl , refl , mE , refl , (refl , mrS) , msS , mΦ)) , mp)
  with ρsp-sound ρsp ρ mρ
... | [I] , mρ` = [] , [I] , _ , 0∈
  , (wkmodβ mβ , (refl , refl , refl , refl , mc , ms , mρ`) , wkmodp mp)

soundness (αρ-spec ρsp@(`IF-Ns x))
  (exc accounts (just (pr current sender
                          ρ@(state en (IF-NONE thn els ; prg) (o ∷ rSI) s`SI))) pending)
  ( mβ , (refl , refl , refl , refl , mc , ms
  , mρ@(refl , refl , mE , refl , (refl , mrS) , msS , mΦ)) , mp)
  with ρsp-sound ρsp ρ mρ
... | [I] , mρ` = [] , [I] , _ , 0∈
  , (wkmodβ mβ , (refl , refl , refl , refl , mc , ms , mρ`) , wkmodp mp)

soundness (αρ-spec ρsp@(ITER'n x))
  (exc accounts (just (pr current sender
                          ρ@(state en (ITER' iterate ∙ prg) rSI (l ∷ s`SI)))) pending)
  ( mβ , (refl , refl , refl , refl , mc , ms
  , mρ@(refl , refl , mE , refl , mrS , (refl , msS) , mΦ)) , mp)
  with ρsp-sound ρsp ρ mρ
... | [I] , mρ` = [] , [I] , _ , 0∈
  , (wkmodβ mβ , (refl , refl , refl , refl , mc , ms , mρ`) , wkmodp mp)

soundness (αρ-spec ρsp@(ITER'c x))
  (exc accounts (just (pr current sender
                          ρ@(state en (ITER' iterate ∙ prg) rSI (l ∷ s`SI)))) pending)
  ( mβ , (refl , refl , refl , refl , mc , ms
  , mρ@(refl , refl , mE , refl , mrS , (refl , msS) , mΦ)) , mp)
  with ρsp-sound ρsp ρ mρ
... | [I] , mρ` = [] , [I] , _ , 0∈
  , (wkmodβ mβ , (refl , refl , refl , refl , mc , ms , mρ`) , wkmodp mp)

soundness (αρ-spec ρsp@(app-bf {args = [ x ]++ args} {bf = bf} `MCargs))
  (exc accounts (just (pr current sender
                          ρ@(state en prg rSI s`SI))) pending)
  ( mβ , (refl , refl , refl , refl , mc , ms
  , mρ@(refl , refl , mE , refl , mrS , msS , mΦ)) , mp)
  with ρsp-sound ρsp ρ mρ
... | γ` , mρ` = [ base _ ] ,  γ` , _ , 0∈
    , wkmodβ mβ , ( refl , refl , refl , refl , wkmodC {γ` = γ`} mc , wkmodC {γ` = γ`} ms
              , mρ`) , wkmodp mp

soundness (no-`NIL no=`NIL)
  (exc accounts nothing [ new-ops , adr // pending ])
  ( mβ , mΦ , (refl , refl , mp))
  with modφ∈Φ no=`NIL mΦ
... | no≡`NIL rewrite no≡`NIL = [] , [I] , _ , 0∈ , mβ , mΦ , mp

soundness {γ = γ} (no-¬sender {new-ops∈ = new-ops∈} s≡nothing)
  (exc accounts nothing [ new-ops , adr // pending ])
  ( mβ , mΦ , (refl , refl , mp))
  with val∈ γ new-ops∈
... | [] = [] , [I] , _ , 0∈ , mβ , mΦ , mp
... | [ transfer-tokens {ty} x x₁ x₂ // nolist ]
  with mβ adr
... | m`MC
  rewrite s≡nothing
  with accounts adr | m`MC
... | nothing | tt
  = [] , [I] , _ , 0∈ , mβ , mΦ , mp

soundness (no-¬p {ty = ty} {cadr = cadr} no=`CONS o=`TRANS cadr=contr c≡just s≡just ty≢p)
  (exc accounts nothing [ new-ops , sadr // pending ])
  ( mβ , mΦ , (refl , refl , mp))
  with modφ∈Φ no=`CONS mΦ | modφ∈Φ o=`TRANS mΦ | modφ∈Φ cadr=contr mΦ | mβ cadr | mβ sadr
... | no≡`CONS | o≡`TRANS | refl | m`MCc | m`MCs
  rewrite no≡`CONS | o≡`TRANS | c≡just | s≡just
  with accounts sadr | m`MCs
... | just (p , _ , sender) | refl , refl , refl , refl , refl , refl , refl
  with sadr ≟ₙ cadr
... | yes refl
  with ty ≟ p
... | yes refl
  = ⊥-elim (ty≢p (,-injectiveˡ (just-injective (trans (sym s≡just) c≡just))))
... | no _ = [] , [I] , _ , 0∈ , mβ , mΦ , (refl , refl , mp)
soundness {γ = γ} (no-¬p {ty = ty} {tok∈ = tok∈} {cadr = cadr}
                         no=`CONS o=`TRANS cadr=contr c≡just s≡just ty≢p)
  (exc accounts nothing [ new-ops , sadr // pending ])
  ( mβ , mΦ , (refl , refl , mp))
    | no≡`CONS | o≡`TRANS | refl | m`MCc | m`MCs
    | just (_ , _ , sender) | refl , refl , refl , refl , refl , refl , refl
    | no  s≢c
  with Contract.balance sender <? val∈ γ tok∈ | accounts cadr | m`MCc
... | yes _ | _ | _ = [] , [I] , _ , 0∈ , mβ , mΦ , (refl , refl , mp)
... | no  _ | just (p , _ , current) | refl , refl , refl , refl , refl , refl , refl
  with ty ≟ p
... | yes refl = ⊥-elim (ty≢p refl)
... | no  _    = [] , [I] , _ , 0∈ , mβ , mΦ , (refl , refl , mp)

soundness (no-¬contr {cadr = cadr} no=`CONS o=`TRANS cadr=contr c≡nothing s≡just)
  (exc accounts nothing [ new-ops , sadr // pending ])
  ( mβ , mΦ , (refl , refl , mp))
  with modφ∈Φ no=`CONS mΦ | modφ∈Φ o=`TRANS mΦ | modφ∈Φ cadr=contr mΦ | mβ cadr | mβ sadr
... | no≡`CONS | o≡`TRANS | refl | m`MCc | m`MCs
  rewrite no≡`CONS | o≡`TRANS | c≡nothing | s≡just
  with accounts sadr | m`MCs
... | just (p , _ , sender) | refl , refl , refl , refl , refl , refl , refl
  with sadr ≟ₙ cadr
... | yes refl
  with trans (sym s≡just) c≡nothing
... | ()
soundness {γ = γ} (no-¬contr {tok∈ = tok∈} {cadr = cadr}
                             no=`CONS o=`TRANS cadr=contr c≡nothing s≡just)
  (exc accounts nothing [ new-ops , sadr // pending ])
  ( mβ , mΦ , (refl , refl , mp))
    | no≡`CONS | o≡`TRANS | refl | m`MCc | m`MCs
    | just (_ , _ , sender) | refl , refl , refl , refl , refl , refl , refl
    | no  s≢c
  with Contract.balance sender <? val∈ γ tok∈ | accounts cadr | m`MCc
... | yes _ | _       | _  = [] , [I] , _ , 0∈ , mβ , mΦ , (refl , refl , mp)
... | no  _ | nothing | tt = [] , [I] , _ , 0∈ , mβ , mΦ , (refl , refl , mp)

soundness {γ = γ} (no-c≡s {x∈ = x∈} {tok∈}
                          no=`CONS o=`TRANS cadr=contr c≡just)
  (exc accounts nothing [ new-ops , adr // pending ])
  ( mβ , mΦ , (refl , refl , mp))
  with modφ∈Φ no=`CONS mΦ | modφ∈Φ o=`TRANS mΦ | modφ∈Φ cadr=contr mΦ | mβ adr
... | no≡`CONS | o≡`TRANS | refl | m`MCc
  rewrite no≡`CONS | o≡`TRANS | c≡just
  with accounts adr | m`MCc
... | just (p , s , sender) | refl , refl , refl , refl , refl , refl , refl
  with adr ≟ₙ adr
... | no  a≢a = ⊥-elim (a≢a refl)
... | yes refl
  with p ≟ p
... | no  p≢p = ⊥-elim (p≢p refl)
... | yes refl
  = [ mutez / (pair p s) ] , 0 ∷ (val∈ γ x∈ , Contract.storage sender) ∷ [I]
  , _ , 0∈ , wkmodβ mβ
           , ( refl , refl , refl , refl
             , (refl , refl , refl , refl , refl)
             , (refl , refl , refl , refl , refl)
             , ( refl , refl , (wkmodβ mβ , refl , refl , refl , refl) , refl
               , (refl , tt) , tt , (refl , refl , wkmodΦ mΦ)))
           , (refl , refl , wkmodp mp)

{-
  -- = {!!}

soundness sp σ mσ = {!!}
-}

soundness {γ = γ} (no-c≢s {x∈ = x∈} {tok∈} {cadr = cadr}
                          no=`CONS o=`TRANS cadr=contr c≡just s≡just cadr≢sadr)
  (exc accounts nothing [ new-ops , sadr // pending ])
  ( mβ , mΦ , (refl , refl , mp))
  with modφ∈Φ no=`CONS mΦ | modφ∈Φ o=`TRANS mΦ | modφ∈Φ cadr=contr mΦ | mβ cadr | mβ sadr
... | no≡`CONS | o≡`TRANS | refl | m`MCc | m`MCs
  rewrite no≡`CONS | o≡`TRANS | c≡just | s≡just
  with accounts sadr | m`MCs
... | just (_ , _ , sender) | refl , refl , refl , refl , refl , refl , refl
  with sadr ≟ₙ cadr
... | yes refl = ⊥-elim (cadr≢sadr refl)
... | no  _
  with Contract.balance sender <? val∈ γ tok∈ | accounts cadr
... | yes b<t | _ = [] , [I] , _ , 0∈ , mβ , (b<t , mΦ) , (refl , refl , mp)
... | no  b≮t | just (p , s , current)
  with m`MCc 
... | refl , refl , refl , refl , refl , refl , refl
  with p ≟ p
... | no  p≢p = ⊥-elim (p≢p refl)
... | yes refl = [ mutez / pair p s ]
               ,  val∈ γ tok∈ + Contract.balance current  ∷
                 (val∈ γ   x∈ , Contract.storage current) ∷ [I]
               , _ , 1∈ , wkmodβ mβ
               , ( refl , refl , refl , refl
                 , (refl , refl , refl , refl , refl)
                 , (refl , refl , refl , refl , refl)
                 , ( refl , refl , (wkmodβ mβ , refl , refl , refl , refl)
                   , refl , (refl , tt) , tt , (refl , refl , ≮⇒≥ b≮t , wkmodΦ mΦ)))
               , (refl , refl , wkmodp mp)

