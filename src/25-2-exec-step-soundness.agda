
module 25-2-exec-step-soundness where

import 00-All-Utilities as H

open import 01-Types
open import 02-Functions-Interpretations
open import 03-2-concrete-execution
open import 11-abstract-representation-and-weakening
open import 12-2-abstract-execution-accessories-and-weakening
open import 13-2-abstract-Prog-state-execution
open import 14-2-abstract-Exec-state-execution
open import 21-2-Prog-state-modeling
open import 22-2-P-s-m-weakening
open import 23-2-prog-step-soundness renaming (soundness to ρ-sound)
open import 24-2-Exec-state-modeling

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality.Core

open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _<_; _≥_; _<ᵇ_; _<?_) renaming (_≟_ to _≟ₙ_)
open import Data.Nat.Properties using (≮⇒≥)
open import Data.List using (List; [] ; _∷_; _++_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product
open import Data.Product.Properties using  (,-injectiveˡ; ,-injectiveʳ; Σ-≡,≡←≡; ×-≡,≡←≡)
open import Data.Sum hiding ([_,_]; map)
open import Data.Sum.Properties using (inj₂-injective)

open import Data.List.Relation.Unary.All using (All; []; _∷_; lookup; lookupAny)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.List.Membership.Propositional using (_∈_)

open import Data.List.Properties
open import Data.Product.Properties

open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)

open import Function using (_|>_; case_of_)

----------------------------------------------------------------------
-- these functions inspect constraints
-- they are sound, but incomplete
----------------------------------------------------------------------
find-ctr-soundness : ∀ {Γ}{t}{P : Passable t} → (Φ : List (Formula Γ)) → (ctr∈ : contract P ∈ Γ)
  → (a : Addr)
  → find-ctr Φ ctr∈ ≡ just a
  → ∀ γ → γ ⊨Φ Φ → val∈ γ ctr∈ ≡ a
find-ctr-soundness ([ x <ₘ x₁ ]++ Φ) ctr∈ a find≡just γ (_ , γ⊨) = find-ctr-soundness Φ ctr∈ a find≡just γ γ⊨
find-ctr-soundness ([ x ≥ₘ x₁ ]++ Φ) ctr∈ a find≡just γ (_ , γ⊨) = find-ctr-soundness Φ ctr∈ a find≡just γ γ⊨
find-ctr-soundness {P = P} ([ _:=_ {tx} x x₁ ]++ Φ) ctr∈ a find≡just γ (_ , γ⊨)
  with tx ≟ contract P
... | no _ = find-ctr-soundness Φ ctr∈ a find≡just γ γ⊨
... | yes refl
  with dec-∈-≡ x ctr∈
... | no _ = find-ctr-soundness Φ ctr∈ a find≡just γ γ⊨
find-ctr-soundness {P = P} ([ _:=_ x (var x₁) ]++ Φ) .x a find≡just γ (γ≡ , γ⊨) | yes refl | yes refl = trans γ≡ (find-ctr-soundness Φ x₁ a find≡just γ γ⊨)
find-ctr-soundness {P = P} ([ _:=_ x (contr x₁) ]++ Φ) .x a find≡just γ (γ≡ , γ⊨) | yes refl | yes refl
  with just-injective find≡just
... | refl = γ≡

----------------------------------------------------------------------
find-tt-soundness : ∀ {Γ}{t}{P : Passable t} → (Φ : List (Formula Γ)) → (op∈ : operation ∈ Γ)
  → (t∈ : t ∈ Γ) → (mut∈ : mutez ∈ Γ) → (ctr∈ : contract P ∈ Γ)
  → find-tt Φ op∈ ≡ just (t , P , [ t∈ ⨾ mut∈ ⨾ ctr∈ ])
  → ∀ (γ : Int Γ) → γ ⊨Φ Φ
  → val∈ γ op∈ ≡ transfer-tokens{t = t}{P = P} (val∈ γ t∈) (val∈ γ mut∈) (val∈ γ ctr∈) 
find-tt-soundness ([ x <ₘ x₁ ]++ Φ) op∈ t∈ mut∈ ctr∈ find≡just γ (_ , γ⊨) = find-tt-soundness Φ op∈ t∈ mut∈ ctr∈ find≡just γ γ⊨
find-tt-soundness ([ x ≥ₘ x₁ ]++ Φ) op∈ t∈ mut∈ ctr∈ find≡just γ (_ , γ⊨) =  find-tt-soundness Φ op∈ t∈ mut∈ ctr∈ find≡just γ γ⊨
find-tt-soundness ([ _:=_ {tx} x x₁ ]++ Φ) op∈ t∈ mut∈ ctr∈ find≡just γ (γ≡ , γ⊨)
  with tx ≟ operation
... | no _ = find-tt-soundness Φ op∈ t∈ mut∈ ctr∈ find≡just γ γ⊨
... | yes refl
  with dec-∈-≡ x op∈
... | no _ = find-tt-soundness Φ op∈ t∈ mut∈ ctr∈ find≡just γ γ⊨
find-tt-soundness ([ _:=_ {.ops} x (var x₁) ]++ Φ) .x t∈ mut∈ ctr∈ find≡just γ (γ≡ , γ⊨) | yes refl | yes refl
  = trans γ≡ (find-tt-soundness Φ x₁ t∈ mut∈ ctr∈ find≡just γ γ⊨)
find-tt-soundness {t = t} {P = P} ([ _:=_ {.ops} x (func (`TRANSFER-TOKENS {pt = P′}) [ px ⨾ px₁ ⨾ px₂ ]) ]++ Φ) x t∈ mut∈ ctr∈ find≡just γ (γ≡ , γ⊨) | yes refl | yes refl
  with just-injective find≡just
... | modσ≡
  with Σ-≡,≡←≡ modσ≡
... | refl , snd≡
  with Σ-≡,≡←≡ snd≡
... | refl , thd≡
  with H.∷-injective px t∈ [ px₁ ⨾ px₂ ] [ mut∈ ⨾ ctr∈ ] thd≡
... | refl , for≡
  with H.∷-injective px₁ mut∈ [ px₂ ] [ ctr∈ ] for≡
... | refl , fth≡
  with H.∷-injective px₂ ctr∈ [] [] fth≡
... | refl , nil≡
  = trans γ≡ refl

----------------------------------------------------------------------
find-tt-list-soundness : ∀ {Γ}{t} → (Φ : List (Formula Γ)) → (l∈ : list t ∈ Γ)
  → find-tt-list Φ l∈ ≡ just (inj₁ [])
  → ∀ (γ : Int Γ) → γ ⊨Φ Φ
  → val∈ γ l∈ ≡ []
find-tt-list-soundness ([ x <ₘ x₁ ]++ Φ) l∈ find≡just γ (_ , γ⊨) = find-tt-list-soundness Φ l∈ find≡just γ γ⊨
find-tt-list-soundness ([ x ≥ₘ x₁ ]++ Φ) l∈ find≡just γ (_ , γ⊨) = find-tt-list-soundness Φ l∈ find≡just γ γ⊨
find-tt-list-soundness {t = t} ([ _:=_ {tx} x x₁ ]++ Φ) l∈ find≡just γ (γ≡ , γ⊨)
  with tx ≟ list t
... | no _ = find-tt-list-soundness Φ l∈ find≡just γ γ⊨
... | yes refl
  with dec-∈-≡ x l∈
... | no _ = find-tt-list-soundness Φ l∈ find≡just γ γ⊨
find-tt-list-soundness {t = t} ([ _:=_ {.(list t)} x (var x₁) ]++ Φ) .x find≡just γ (γ≡ , γ⊨) | yes refl | yes refl
  = trans γ≡ (find-tt-list-soundness Φ x₁ find≡just γ γ⊨)
find-tt-list-soundness {t = t} ([ _:=_ {.(list t)} x (func (`NIL .t) x₂) ]++ Φ) x find≡just γ (γ≡ , γ⊨) | yes refl | yes refl
  with just-injective find≡just
... | refl
  = γ≡

----------------------------------------------------------------------
find-tt-list-cons-soundness : ∀ {Γ}{t} → (Φ : List (Formula Γ)) → (l∈ : list t ∈ Γ)
  → (head∈ : t ∈ Γ)
  → (rest∈ : list t ∈ Γ)
  → find-tt-list Φ l∈ ≡ just (inj₂ [ head∈ ⨾ rest∈ ])
  → ∀ (γ : Int Γ) → γ ⊨Φ Φ
  → val∈ γ l∈ ≡ val∈ γ head∈ ∷ val∈ γ rest∈
find-tt-list-cons-soundness ([ x <ₘ x₁ ]++ Φ) l∈ head∈ rest∈ find≡just γ (_ , γ⊨) = find-tt-list-cons-soundness Φ l∈ head∈ rest∈ find≡just γ γ⊨
find-tt-list-cons-soundness ([ x ≥ₘ x₁ ]++ Φ) l∈ head∈ rest∈ find≡just γ (_ , γ⊨) = find-tt-list-cons-soundness Φ l∈ head∈ rest∈ find≡just γ γ⊨
find-tt-list-cons-soundness {t = t} ([ _:=_ {tx} x x₁ ]++ Φ) l∈ head∈ rest∈ find≡just γ (γ≡ , γ⊨)
  with tx ≟ list t
... | no _ = find-tt-list-cons-soundness Φ l∈ head∈ rest∈ find≡just γ γ⊨
... | yes refl
  with dec-∈-≡ x l∈
... | no _ = find-tt-list-cons-soundness Φ l∈ head∈ rest∈ find≡just γ γ⊨
find-tt-list-cons-soundness {t = t} ([ _:=_ {.(list t)} x (var x₁) ]++ Φ) .x head∈ rest∈ find≡just γ (γ≡ , γ⊨) | yes refl | yes refl
  = trans γ≡ (find-tt-list-cons-soundness Φ x₁ head∈ rest∈ find≡just γ γ⊨)
find-tt-list-cons-soundness {t = t} ([ _:=_ {.(list t)} x (func `CONS [ t-∈ ⨾ list-t-∈ ]) ]++ Φ) x head∈ rest∈ find≡just γ (γ≡ , γ⊨) | yes refl | yes refl
  with just-injective find≡just
... | just-find≡just
  with inj₂-injective just-find≡just
... | inj₂-just-find≡just
  with H.∷-injective t-∈ head∈ [ list-t-∈ ] [ rest∈ ] inj₂-just-find≡just
... | refl , rest≡
  with H.∷-injective list-t-∈ rest∈ [] [] rest≡
... | refl , nil≡
  = trans γ≡ refl

----------------------------------------------------------------------
transfer-tokens-injective : ∀ {t₁ t₂}{P₁ : Passable t₁}{P₂ : Passable t₂} {x₁ : ⟦ t₁ ⟧} {y₁ : ⟦ t₂ ⟧} {x₂ y₂} {x₃ y₃}
  → transfer-tokens{t₁}{P₁} x₁ x₂ x₃ ≡ transfer-tokens{t₂}{P₂} y₁ y₂ y₃
  → Σ (t₁ ≡ t₂) λ{ refl → Σ (P₁ ≡ P₂) λ{ refl
  → x₁ ≡ y₁ × x₂ ≡ y₂ × x₃ ≡ y₃}}
transfer-tokens-injective refl = refl , refl , refl , refl , refl
----------------------------------------------------------------------

¬is-cons-[] : ∀ {a}{A : Set a} {x : A} {xs : List A} → ¬ ([] ≡ x ∷ xs)
¬is-cons-[] ()
----------------------------------------------------------------------

lemma-addresses : ∀ {Γ} → (αccounts : Abstract Blockchain Γ)
                        → (accounts : Concrete Blockchain)
                        → (γ : All ⟦_⟧ Γ)
                        → (mβ        : (a : ℕ) → mod`MC γ (αccounts a) (accounts a))
                        → (a : Addr)
                        → (αccounts a ≡ nothing × accounts a ≡ nothing)
                        ⊎ (∃[ αa ] ∃[ aa ] αccounts a ≡ just αa
                                         × accounts a ≡ just aa
                                         × Σ (proj₁ αa ≡ proj₁ aa) λ{ refl
                                         → Σ (proj₁ (proj₂ αa) ≡ proj₁ (proj₂ aa)) λ{ refl
                                         → modC γ (proj₂ (proj₂ αa)) (proj₂ (proj₂ aa))}})
lemma-addresses αccounts accounts γ mβ a
  with αccounts a | accounts a | mβ a
... | nothing | nothing | tt
  = inj₁ (refl , refl)
lemma-addresses αccounts accounts γ mβ a | just αa@(αp , αs , αC) | just aa@(cp , cs , cC) | (refl , refl , modc)
  = inj₂ (αa , (aa , (refl , refl , (refl , refl , modc))))

----------------------------------------------------------------------

soundness : ∀ {Γ} (γ : Int Γ) → ∀ ασ σ → modσ γ ασ σ
          → ∃[ Φ ] ExecState.MPstate ασ ≡ `APanic Φ
          ⊎ ∃[ Γ` ] ∃[ γ` ] mod⊎σ {Γ` ++ Γ} (γ` +I+ γ) (αexec-step ασ) (exec-step σ)

soundness γ ασ@(exc αccounts (`AFail Φ) αpending)
            (exc accounts (Fail tt) pending)
            mσ = inj₂ ([] , [] , ασ , (here refl) , mσ)

soundness γ (exc αccounts (`APanic Φ)  αpending)
            (exc accounts (Cont tt) pending)
            mσ = inj₁ (Φ , refl)

soundness γ ασ@(exc αccounts (`INJ₂ Φ) [I]) (exc accounts (`INJ₂ tt) [I]) modσ⟨ mβ , mr , tt ⟩
  =  inj₂ (_ , [] , (ασ , (here refl , (mβ , (mr , tt)))))
soundness γ (exc αccounts (`INJ₂ Φ) [I]) (exc accounts (`INJ₂ tt) ([ x ]++ pending)) modσ⟨ mβ , mr , () ⟩
soundness γ (exc αccounts (`INJ₂ Φ) ([ x ]++ αpending)) (exc accounts (`INJ₂ tt) [I]) modσ⟨ mβ , mr , () ⟩
soundness {Γ = Γ} γ
          ασ@(exc αccounts (`INJ₂ Φ) ([ pops , send-addr ]++ αpending))
          σ@(exc accounts (`INJ₂ tt) ([ .(val∈ γ pops) , .send-addr ]++ pending))
          modσ⟨ mβ , mr , modσ⟨ refl , refl , mp ⟩ ⟩
  with lemma-addresses αccounts accounts γ mβ send-addr
... | inj₁ (anothing , cnothing) rewrite anothing | cnothing
  = inj₂ ([] , [] , record ασ{ pending = αpending ; MPstate = `AFail Φ }
         , ((here refl)
         , (mβ
         , (mr 
         , mp))))
... | inj₂ ((ap , as , asender) , (cp , cs , cc) , ajust , cjust , refl , refl
           , modC⟨ refl , send-store≡ ⟩ )
  rewrite ajust | cjust
  with find-tt-list Φ pops in find-tt-list-eq
... | nothing
  = inj₂ ([] , [] , (record ασ{ MPstate = `APanic Φ } , (here refl , tt)))

... | just (inj₁ [])
  rewrite find-tt-list-soundness Φ pops find-tt-list-eq γ mr
  = inj₂ ([] , [] , record ασ{ pending = αpending } , here refl , mβ , mr , mp)

... | just (inj₂ [ op∈ ⨾ rest∈ ])
  with find-tt Φ op∈ in find-tt-eq
... | nothing
  = inj₂ ([] , [] , record ασ{ MPstate = `APanic Φ } , here refl , tt)
... | just (expected-param-ty , P , [ param∈Γ ⨾ amount∈Γ ⨾ contr∈Γ ])
  with find-tt-soundness Φ op∈ param∈Γ amount∈Γ contr∈Γ find-tt-eq γ mr
... | op∈≡transfer-tokens
  with find-ctr Φ contr∈Γ in find-ctr-eq
... | nothing
  = inj₂ ([] , [] , record ασ{ MPstate = `APanic Φ } , here refl , tt)
... | just self-addr
  with αccounts self-addr | accounts self-addr in csa-eq | mβ self-addr
... | nothing | nothing | tt
  =  inj₂ ([] , [] , record ασ{ MPstate = `APanic Φ } , here refl , tt)
... | just ∃self@(param-ty , store-ty , self) | just ∃cself@(cparam-ty , cstore-ty , cself) | refl , refl , modC⟨ modBal , modSto ⟩
  with find-tt-list-cons-soundness Φ pops op∈ rest∈ find-tt-list-eq γ mr
... | cons-soundness
  with val∈ γ pops in pops≡
... | [] = ⊥-elim (¬is-cons-[] cons-soundness)
... | transfer-tokens xx yy zz ∷ rest-ops
  with ∷-injective cons-soundness
... | tt≡ , rest-ops≡
  with trans tt≡ op∈≡transfer-tokens
... | refl
--   with transfer-tokens-injective (trans tt≡ op∈≡transfer-tokens)
-- ... | refl , refl , xx≡ , refl , zz≡
--
  with expected-param-ty ≟ param-ty in exp-ty-eq
... | no _
  = inj₂ ([] , [] , record ασ{ MPstate = `APanic Φ } , here refl , tt)
... | yes refl
  with Contract.balance cc <? yy
... | yes is-less
  = inj₂ ( []
         , []
         , exc αccounts
               (`AFail (Contract.balance asender <ₘ amount∈Γ ∷ Φ))
               [ rest∈ , send-addr // αpending ]
         , here refl
         , mβ
         , (is-less , mr)
         , sym rest-ops≡
         , refl
         , mp)
... | no is-not-less
  rewrite find-ctr-soundness Φ contr∈Γ self-addr find-ctr-eq γ mr
  with self-addr ≟ₙ send-addr in self-send-eq
... | yes refl
  rewrite csa-eq | exp-ty-eq | self-send-eq
  = 
      let sender-balance = val∈ γ (Contract.balance asender)
          amount         = val∈ γ amount∈Γ
      in  inj₂ ( [ pair param-ty store-ty ]
               , [ val∈ γ param∈Γ , val∈ γ (Contract.storage self) ]
               , _
               , there (here refl)
               , modσ⟨ wkmodβ mβ
                     , (refl , refl , refl , refl , (modC⟨ modBal , modSto ⟩ ,
                                                    (modC⟨ refl , send-store≡ ⟩ ,
                                                     modρ⟨ modE⟨ wkmodβ mβ , modBal , refl ⟩
                                                         , (×-≡,≡→≡ (refl , modSto) , tt)
                                                         , (modprg-extend (Contract.program cself) tt)
                                                         , (refl , (≮⇒≥ is-not-less , wkmodΦ mr)) ⟩)))
                     , (sym rest-ops≡ , (refl , wkmodp mp)) ⟩)
... | no _
  rewrite csa-eq | exp-ty-eq | self-send-eq
  = let sender-balance = val∈ γ (Contract.balance asender)
        amount         = val∈ γ amount∈Γ
        self-balance   = val∈ γ (Contract.balance self)
        comparison     = sender-balance <ᵇ amount
    in  inj₂ ( [ pair param-ty store-ty ⨾ mutez ⨾ mutez ]
             , [  val∈ γ param∈Γ , val∈ γ (Contract.storage self)
               ⨾ amount + self-balance
               ⨾ sender-balance ∸ amount ]
             , _
             , there (here refl)
             , modσ⟨ {!!}
                   , (refl , refl , refl , refl , modC⟨ cong₂ _+_ refl modBal , modSto ⟩ ,
                                                  modC⟨ refl , send-store≡ ⟩ ,
                                                  modρ⟨ modE⟨ {!!} , cong₂ _+_ refl modBal , refl ⟩
                                                      , (×-≡,≡→≡ (refl , modSto) , tt)
                                                      , modprg-extend (Contract.program cself) tt
                                                      , (refl , (refl , (refl , (≮⇒≥ is-not-less , wkmodΦ mr)))) ⟩)
                   , (sym rest-ops≡ , (refl , wkmodp mp)) ⟩)




soundness γ _ _ _ = {!!}

-- soundness γ
--   (exc αccounts
--         (`INJ₁ (pr {ss = s} αself αsender (state
--           (env _  cadr  sadr blc∈ amn∈) end (no,ns∈ ∷ [M]) [M] Φ)))
--         αpending)
--    (exc accounts
--         (`INJ₁ (pr self sender (state
--            (env _ .cadr .sadr blc  amn) .end ((n-ops , n-stor) ∷ [I]) [I] tt)))
--         pending)
--    ( mβ
--    , ( refl , refl , refl , refl
--      , (refl , refl , refl , refl , refl) , (refl , refl , refl , refl , refl)
--      , refl , refl , (_ , refl , refl , refl , refl) , refl , (refl , tt) , tt , mΦ)
--    , mp)
--   = inj₂ (_ , n-ops ∷ n-stor ∷ [I] , _ , 0∈ ,
--   ( modset cadr (refl , refl , refl , refl , refl) (wkmodβ mβ)
--   , (refl , refl , wkmodΦ mΦ)
--   , wkmodp mp +modp+ refl , refl))

-- soundness {Γ} γ ασ@(exc αccounts (`INJ₁ (pr {ss = s} αself αsender αρ@(state αen
--     (enf `AMOUNT ; prg) r`VM s`VM Φ))) αpending)
--   σ@(exc accounts (`INJ₁ (pr self sender ρ)) pending)
--   ( mβ , (refl , refl , refl , refl , mc , ms , mρ@(refl , refl , mE , refl , mρrest))
--   , mp)
--   with ρ-sound γ αρ ρ mρ
-- ... | Γ` , γ` , _ , here px , mρ` with ++-cancelʳ Γ Γ` [] (,-injectiveˡ px)
-- soundness γ ασ σ (mβ , ( refl , refl , refl , refl , mc , ms , mρ) , mp)
--   | _ , γ` , _ , 0∈ , mρ` | refl
--   = inj₂ ( _ , γ` , _ , 0∈ , (wkmodβ mβ) , (refl , refl , refl , refl
--          , wkmodC {γ` = γ`} mc , (wkmodC {γ` = γ`} ms) , mρ`) , wkmodp mp)

-- soundness {Γ} γ ασ@(exc αccounts (`INJ₁ (pr {ss = s} αself αsender αρ@(state αen
--     (enf `BALANCE ; prg) r`VM s`VM Φ))) αpending)
--   σ@(exc accounts (`INJ₁ (pr self sender ρ)) pending)
--   ( mβ , (refl , refl , refl , refl , mc , ms , mρ@(refl , refl , mE , refl , mρrest))
--   , mp)
--   with ρ-sound γ αρ ρ mρ
-- ... | Γ` , γ` , _ , here px , mρ` with ++-cancelʳ Γ Γ` [] (,-injectiveˡ px)
-- soundness γ ασ σ (mβ , ( refl , refl , refl , refl , mc , ms , mρ) , mp)
--   | _ , γ` , _ , 0∈ , mρ` | refl
--   = inj₂ ( _ , γ` , _ , 0∈ , (wkmodβ mβ) , (refl , refl , refl , refl
--          , wkmodC {γ` = γ`} mc , (wkmodC {γ` = γ`} ms) , mρ`) , wkmodp mp)

-- soundness {Γ} γ ασ@(exc αccounts (`INJ₁ (pr {ss = s} αself αsender αρ@(state αen
--     (enf (`CONTRACT P) ; prg) (v∈ ∷ r`VM) s`VM Φ))) αpending)
--   σ@(exc accounts (`INJ₁ (pr self sender ρ)) pending)
--   ( mβ , (refl , refl , refl , refl , mc , ms , mρ@(refl , refl , mE , refl , mρrest))
--   , mp)
--   with ρ-sound γ αρ ρ mρ
-- ... | Γ` , γ` , _ , here px , mρ`
--   with ++-cancelʳ Γ Γ` [ option (contract P) ] (,-injectiveˡ px)
-- soundness γ ασ σ (mβ , ( refl , refl , refl , refl , mc , ms , mρ) , mp)
--   | _ , γ` , _ , 0∈ , mρ` | refl
--   = inj₂ ( _ , γ` , _ , 0∈ , (wkmodβ mβ) , (refl , refl , refl , refl
--          , wkmodC {γ` = γ`} mc , (wkmodC {γ` = γ`} ms) , mρ`) , wkmodp mp)

-- soundness {Γ} γ ασ@(exc αccounts (`INJ₁ (pr {ss = s} αself αsender αρ@(state αen
--     (fct (D1 {result = result} x) ; prg) r`VM s`VM Φ))) αpending)
--   σ@(exc accounts (`INJ₁ (pr self sender ρ)) pending)
--   ( mβ , (refl , refl , refl , refl , mc , ms , mρ@(refl , refl , mE , refl , mρrest))
--   , mp)
--   with ρ-sound γ αρ ρ mρ
-- ... | Γ` , γ` , _ , here px , mρ` with ++-cancelʳ Γ Γ` [ result ] (,-injectiveˡ px)
-- soundness γ ασ σ (mβ , ( refl , refl , refl , refl , mc , ms , mρ) , mp)
--   | _ , γ` , _ , 0∈ , mρ` | refl
--   = inj₂ ( _ , γ` , _ , 0∈ , (wkmodβ mβ) , (refl , refl , refl , refl
--          , wkmodC {γ` = γ`} mc , (wkmodC {γ` = γ`} ms) , mρ`) , wkmodp mp)

-- soundness {Γ} γ ασ@(exc αccounts (`INJ₁ (pr {ss = s} αself αsender αρ@(state αen
--     (fct (Dm (`UNPAIR {ty₁} {ty₂})) ; prg) (v∈ ∷ r`VM) s`VM Φ))) αpending)
--   σ@(exc accounts (`INJ₁ (pr self sender ρ)) pending)
--   ( mβ , (refl , refl , refl , refl , mc , ms , mρ@(refl , refl , mE , refl , mρrest))
--   , mp)
--   with ρ-sound γ αρ ρ mρ
-- ... | Γ` , γ` , _ , here px , mρ` with ++-cancelʳ Γ Γ` [ ty₁ / ty₂ ] (,-injectiveˡ px)
-- soundness γ ασ σ (mβ , ( refl , refl , refl , refl , mc , ms , mρ) , mp)
--   | _ , γ` , _ , 0∈ , mρ` | refl
--   = inj₂ ( _ , γ` , _ , 0∈ , (wkmodβ mβ) , (refl , refl , refl , refl
--          , wkmodC {γ` = γ`} mc , (wkmodC {γ` = γ`} ms) , mρ`) , wkmodp mp)

-- soundness {Γ} γ ασ@(exc αccounts (`INJ₁ (pr {ss = s} αself αsender αρ@(state αen
--     (fct (Dm `SWAP) ; prg) (v∈ ∷ w∈ ∷ r`VM) s`VM Φ))) αpending)
--   σ@(exc accounts (`INJ₁ (pr self sender ρ)) pending)
--   ( mβ , (refl , refl , refl , refl , mc , ms , mρ@(refl , refl , mE , refl , mρrest))
--   , mp)
--   with ρ-sound γ αρ ρ mρ
-- ... | Γ` , γ` , _ , here px , mρ` with ++-cancelʳ Γ Γ` [] (,-injectiveˡ px)
-- soundness γ ασ σ (mβ , ( refl , refl , refl , refl , mc , ms , mρ) , mp)
--   | _ , γ` , _ , 0∈ , mρ` | refl
--   = inj₂ ( _ , γ` , _ , 0∈ , (wkmodβ mβ) , (refl , refl , refl , refl
--          , wkmodC {γ` = γ`} mc , (wkmodC {γ` = γ`} ms) , mρ`) , wkmodp mp)

-- soundness {Γ} γ ασ@(exc αccounts (`INJ₁ (pr {ss = s} αself αsender αρ@(state αen
--     (fct (Dm `DUP) ; prg) (v∈ ∷ r`VM) s`VM Φ))) αpending)
--   σ@(exc accounts (`INJ₁ (pr self sender ρ)) pending)
--   ( mβ , (refl , refl , refl , refl , mc , ms , mρ@(refl , refl , mE , refl , mρrest))
--   , mp)
--   with ρ-sound γ αρ ρ mρ
-- ... | Γ` , γ` , _ , here px , mρ` with ++-cancelʳ Γ Γ` [] (,-injectiveˡ px)
-- soundness γ ασ σ (mβ , ( refl , refl , refl , refl , mc , ms , mρ) , mp)
--   | _ , γ` , _ , 0∈ , mρ` | refl
--   = inj₂ ( _ , γ` , _ , 0∈ , (wkmodβ mβ) , (refl , refl , refl , refl
--          , wkmodC {γ` = γ`} mc , (wkmodC {γ` = γ`} ms) , mρ`) , wkmodp mp)

-- soundness {Γ} γ ασ@(exc αccounts (`INJ₁ (pr {ss = s} αself αsender αρ@(state αen
--     (fct (`PUSH P x) ; prg) r`VM s`VM Φ))) αpending)
--   σ@(exc accounts (`INJ₁ (pr self sender ρ)) pending)
--   ( mβ , (refl , refl , refl , refl , mc , ms , mρ@(refl , refl , mE , refl , mρrest))
--   , mp)
--   with ρ-sound γ αρ ρ mρ
-- ... | Γ` , γ` , _ , here px , mρ` with ++-cancelʳ Γ Γ` (expandΓ P x) (,-injectiveˡ px)
-- soundness γ ασ σ (mβ , ( refl , refl , refl , refl , mc , ms , mρ) , mp)
--   | _ , γ` , _ , 0∈ , mρ` | refl
--   = inj₂ ( _ , γ` , _ , 0∈ , (wkmodβ mβ) , (refl , refl , refl , refl
--          , wkmodC {γ` = γ`} mc , (wkmodC {γ` = γ`} ms) , mρ`) , wkmodp mp)

-- soundness {Γ} γ ασ@(exc αccounts (`INJ₁ (pr {ss = s} αself αsender αρ@(state αen
--     (DROP ; prg) (v∈ ∷ r`VM) s`VM Φ))) αpending)
--   σ@(exc accounts (`INJ₁ (pr self sender ρ)) pending)
--   ( mβ , (refl , refl , refl , refl , mc , ms , mρ@(refl , refl , mE , refl , mρrest))
--   , mp)
--   with ρ-sound γ αρ ρ mρ
-- ... | Γ` , γ` , _ , here px , mρ` with ++-cancelʳ Γ Γ` [] (,-injectiveˡ px)
-- soundness γ ασ σ (mβ , ( refl , refl , refl , refl , mc , ms , mρ) , mp)
--   | _ , γ` , _ , 0∈ , mρ` | refl
--   = inj₂ ( _ , γ` , _ , 0∈ , (wkmodβ mβ) , (refl , refl , refl , refl
--          , wkmodC {γ` = γ`} mc , (wkmodC {γ` = γ`} ms) , mρ`) , wkmodp mp)

-- soundness {Γ} γ ασ@(exc αccounts (`INJ₁ (pr {ss = s} αself αsender αρ@(state αen
--     (ITER x ; prg) (v∈ ∷ r`VM) s`VM Φ))) αpending)
--   σ@(exc accounts (`INJ₁ (pr self sender ρ)) pending)
--   ( mβ , (refl , refl , refl , refl , mc , ms , mρ@(refl , refl , mE , refl , mρrest))
--   , mp)
--   with ρ-sound γ αρ ρ mρ
-- ... | Γ` , γ` , _ , here px , mρ` with ++-cancelʳ Γ Γ` [] (,-injectiveˡ px)
-- soundness γ ασ σ (mβ , ( refl , refl , refl , refl , mc , ms , mρ) , mp)
--   | _ , γ` , _ , 0∈ , mρ` | refl
--   = inj₂ ( _ , γ` , _ , 0∈ , (wkmodβ mβ) , (refl , refl , refl , refl
--          , wkmodC {γ` = γ`} mc , (wkmodC {γ` = γ`} ms) , mρ`) , wkmodp mp)

-- soundness {Γ} γ ασ@(exc αccounts (`INJ₁ (pr {ss = s} αself αsender αρ@(state αen
--     (DIP n x ; prg) r`VM s`VM Φ))) αpending)
--   σ@(exc accounts (`INJ₁ (pr self sender ρ)) pending)
--   ( mβ , (refl , refl , refl , refl , mc , ms , mρ@(refl , refl , mE , refl , mρrest))
--   , mp)
--   with ρ-sound γ αρ ρ mρ
-- ... | Γ` , γ` , _ , here px , mρ` with ++-cancelʳ Γ Γ` [] (,-injectiveˡ px)
-- soundness γ ασ σ (mβ , ( refl , refl , refl , refl , mc , ms , mρ) , mp)
--   | _ , γ` , _ , 0∈ , mρ` | refl
--   = inj₂ ( _ , γ` , _ , 0∈ , (wkmodβ mβ) , (refl , refl , refl , refl
--          , wkmodC {γ` = γ`} mc , (wkmodC {γ` = γ`} ms) , mρ`) , wkmodp mp)

-- soundness {Γ} γ ασ@(exc αccounts (`INJ₁ (pr {ss = s} αself αsender αρ@(state αen
--     (IF-NONE thn els ; prg) (v∈ ∷ r`VM) s`VM Φ))) αpending)
--   σ@(exc accounts (`INJ₁ (pr self sender ρ)) pending)
--   ( mβ , (refl , refl , refl , refl , mc , ms , mρ@(refl , refl , mE , refl , mρrest))
--   , mp)
--   with ρ-sound γ αρ ρ mρ
-- ... | Γ` , γ` , _ , here px , mρ` with ++-cancelʳ Γ Γ` [] (,-injectiveˡ px)
-- soundness γ ασ σ (mβ , ( refl , refl , refl , refl , mc , ms , mρ) , mp)
--   | _ , γ` , _ , 0∈ , mρ` | refl
--   = inj₂ ( _ , γ` , _ , 0∈ , (wkmodβ mβ) , (refl , refl , refl , refl
--          , wkmodC {γ` = γ`} mc , (wkmodC {γ` = γ`} ms) , mρ`) , wkmodp mp)
-- soundness {Γ} γ ασ@(exc αccounts (`INJ₁ (pr {ss = s} αself αsender αρ@(state αen
--     (IF-NONE {t = t} thn els ; prg) (v∈ ∷ r`VM) s`VM Φ))) αpending)
--   σ (mβ , ( refl , refl , refl , refl , mc , ms , mρ) , mp)
--   | Γ` , γ` , _ , there (here px) , mρ` with ++-cancelʳ Γ Γ` [ t ] (,-injectiveˡ px)
-- soundness γ ασ σ (mβ , ( refl , refl , refl , refl , mc , ms , mρ) , mp)
--   | _ , γ` , _ , 1∈ , mρ` | refl
--   = inj₂ ( _ , γ` , _ , 1∈ , (wkmodβ mβ) , (refl , refl , refl , refl
--          , wkmodC {γ` = γ`} mc , (wkmodC {γ` = γ`} ms) , mρ`) , wkmodp mp)

-- soundness {Γ} γ ασ@(exc αccounts (`INJ₁ (pr {ss = s} αself αsender αρ@(state αen
--     (ITER' x ∙ prg) r`VM (v∈ ∷ s`VM) Φ))) αpending)
--   σ@(exc accounts (`INJ₁ (pr self sender ρ)) pending)
--   ( mβ , (refl , refl , refl , refl , mc , ms , mρ@(refl , refl , mE , refl , mρrest))
--   , mp)
--   with ρ-sound γ αρ ρ mρ
-- ... | Γ` , γ` , _ , here px , mρ` with ++-cancelʳ Γ Γ` [] (,-injectiveˡ px)
-- soundness γ ασ σ (mβ , ( refl , refl , refl , refl , mc , ms , mρ) , mp)
--   | _ , γ` , _ , 0∈ , mρ` | refl
--   = inj₂ ( _ , γ` , _ , 0∈ , (wkmodβ mβ) , (refl , refl , refl , refl
--          , wkmodC {γ` = γ`} mc , (wkmodC {γ` = γ`} ms) , mρ`) , wkmodp mp)
-- soundness {Γ} γ ασ@(exc αccounts (`INJ₁ (pr {ss = s} αself αsender αρ@(state αen
--     (ITER' {ty} x ∙ prg) r`VM (v∈ ∷ s`VM) Φ))) αpending)
--   σ (mβ , ( refl , refl , refl , refl , mc , ms , mρ) , mp)
--   | Γ` , γ` , _ , there (here px) , mρ`
--   with ++-cancelʳ Γ Γ` [ ty / list ty ] (,-injectiveˡ px)
-- soundness γ ασ σ (mβ , ( refl , refl , refl , refl , mc , ms , mρ) , mp)
--   | _ , γ` , _ , 1∈ , mρ` | refl
--   = inj₂ ( _ , γ` , _ , 1∈ , (wkmodβ mβ) , (refl , refl , refl , refl
--          , wkmodC {γ` = γ`} mc , (wkmodC {γ` = γ`} ms) , mρ`) , wkmodp mp)

-- soundness {Γ} γ ασ@(exc αccounts (`INJ₁ (pr {ss = s} αself αsender αρ@(state αen
--     (DIP' top ∙ prg) r`VM s`VM Φ))) αpending)
--   σ@(exc accounts (`INJ₁ (pr self sender ρ)) pending)
--   ( mβ , (refl , refl , refl , refl , mc , ms , mρ@(refl , refl , mE , refl , mρrest))
--   , mp)
--   with ρ-sound γ αρ ρ mρ
-- ... | Γ` , γ` , _ , here px , mρ` with ++-cancelʳ Γ Γ` [] (,-injectiveˡ px)
-- soundness γ ασ σ (mβ , ( refl , refl , refl , refl , mc , ms , mρ) , mp)
--   | _ , γ` , _ , 0∈ , mρ` | refl
--   = inj₂ ( _ , γ` , _ , 0∈ , (wkmodβ mβ) , (refl , refl , refl , refl
--          , wkmodC {γ` = γ`} mc , (wkmodC {γ` = γ`} ms) , mρ`) , wkmodp mp)

-- -----------------------------------------------------------------------------------------

