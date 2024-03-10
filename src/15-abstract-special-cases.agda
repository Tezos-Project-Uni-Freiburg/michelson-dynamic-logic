
module 15-abstract-special-cases where

open import 01-Types
open import 02-Functions-Interpretations
open import 03-concrete-execution
open import 11-abstract-representation-and-weakening
open import 12-abstract-execution-accessories-and-weakening 

open import Relation.Binary.PropositionalEquality.Core

open import Data.List.Base hiding ([_]; unfold)
open import Data.Maybe.Base hiding (map)
open import Data.Product hiding (map)
open import Data.Sum hiding ([_,_]; map)

open import Data.List.Relation.Unary.All using (All; _∷_; [])
open import Data.List.Relation.Unary.Any hiding (map)
open import Data.List.Membership.Propositional using (_∈_)


------------------------- special cases for abstract state transitions ------------------

-- this is another list like strucuter parameterized by a list of formulas Φ and indexed
-- by a Match to express the circumstances that for every variable in the given Match
-- there exists a formula in Φ that sets this variable equal to a constant term
-- (this implies that the Match is on primitive types only)
data MatchConst {Γ} (Φ : List (Formula Γ)) : ∀ {S} → Match Γ S → Set where
  [MC] : MatchConst Φ [M]
  _∷_  : ∀ {bt x S M} {v∈ : base bt ∈ Γ} 
       → (v∈ := const x) ∈ Φ →  MatchConst Φ {S} M → MatchConst Φ (v∈ ∷ M)

-- from such a Match we can extract an Int of the same Stack since all values are
-- provided in Φ
getInt : ∀ {Γ Φ S M} → MatchConst {Γ} Φ {S} M → Int S
getInt [MC] = [I]
getInt (_∷_ {x = x} v∈:=const MC) = x ∷ (getInt MC)

-- while αprog-step can always be executed, it may be beneficial to use this special
-- transition relation that exploits additional information from Φ and sometimes the
-- environment (examples are explained in the thesis in section 4.3)
data αρ-special {Γ ro so} :         αProg-state        Γ  ro so
                          → ∃[ Γ` ] αProg-state (Γ` ++ Γ) ro so → Set where

  CAR    : ∀ {αen ty₁ ty₂ v₁∈ v₂∈ S si p∈ Φ prg rVM sVM}
         → p∈ := func (PAIR {ty₁} {ty₂}) (v₁∈ ∷ v₂∈ ∷ [M])  ∈  Φ
         → αρ-special 
                (αstate {si = si} αen (fct {S = S} (D1 CAR) ; prg)  (p∈ ∷ rVM) sVM Φ)
           ([] , αstate           αen                         prg  (v₁∈ ∷ rVM) sVM Φ)

  CDR    : ∀ {αen ty₁ ty₂ v₁∈ v₂∈ S si p∈ Φ prg rVM sVM}
         → p∈ := func (PAIR {ty₁} {ty₂}) (v₁∈ ∷ v₂∈ ∷ [M])  ∈  Φ
         → αρ-special 
                (αstate {si = si} αen (fct {S = S} (D1 CDR) ; prg)  (p∈ ∷ rVM) sVM Φ)
           ([] , αstate           αen                         prg  (v₂∈ ∷ rVM) sVM Φ)

  UNPAIR : ∀ {αen ty₁ ty₂ v₁∈ v₂∈ S si p∈ Φ prg rVM sVM}
         → p∈ := func (PAIR {ty₁} {ty₂}) (v₁∈ ∷ v₂∈ ∷ [M])  ∈  Φ
         → αρ-special 
                (αstate {si = si} αen (fct {S = S} (Dm UNPAIR) ; prg) (p∈ ∷ rVM) sVM Φ)
           ([] , αstate           αen                      prg (v₁∈ ∷ v₂∈ ∷ rVM) sVM Φ)

  CTRn   : ∀ {adr∈ adr Φ αen p S si P prg rVM sVM}
         → adr∈ := const adr  ∈  Φ
         → αEnvironment.αccounts αen adr ≡ nothing
         → αρ-special 
               (αstate {si = si} αen (enf {S = S} (CONTRACT {p} P) ; prg)
                (adr∈ ∷ rVM) sVM Φ)
           ([ option (contract P) ] ,
                αstate (wkαE αen) prg (0∈ ∷ wkM rVM) (wkM sVM)
                       [ 0∈ := func (NONE (contract P)) [M] // wkΦ Φ ])

  CTR¬p  : ∀ {adr∈ adr Φ αen p s αc S si p' P prg rVM sVM}
         → adr∈ := const adr  ∈  Φ
         → αEnvironment.αccounts αen adr ≡ just (p , s , αc)
         → p ≢ p'
         → αρ-special 
               (αstate {si = si} αen (enf {S = S} (CONTRACT {p'} P) ; prg)
                (adr∈ ∷ rVM) sVM Φ)
           ([ option (contract P) ] ,
                αstate (wkαE αen) prg (0∈ ∷ wkM rVM) (wkM sVM)
                       [ 0∈ := func (NONE (contract P)) [M] // wkΦ Φ ])

  CTRjp  : ∀ {adr∈ adr Φ αen p s αc S si P prg rVM sVM}
         → adr∈ := const adr  ∈  Φ
         → αEnvironment.αccounts αen adr ≡ just (p , s , αc)
         → αρ-special 
               (αstate {si = si} αen (enf {S = S} (CONTRACT {p} P) ; prg)
                (adr∈ ∷ rVM) sVM Φ)
           ([ contract P / option (contract P) ] ,
                αstate (wkαE αen) prg (1∈ ∷ wkM rVM) (wkM sVM)
                       [ 0∈ := contr adr / 1∈ := func SOME (0∈ ∷ [M]) // wkΦ Φ ])

  IF-Nn  : ∀ {αen ty o∈ Φ si S Se thn els prg rVM sVM}
         → o∈ := func (NONE ty) [M]  ∈  Φ
         → αρ-special 
                (αstate {si = si} αen (IF-NONE {ty} {S} {Se}
                                       thn els ;  prg) (o∈ ∷ rVM) sVM Φ)
           ([] , αstate           αen     (thn ;∙ prg)       rVM  sVM Φ)

  IF-Ns  : ∀ {αen ty o∈ x∈ Φ si S Se thn els prg rVM sVM}
         → o∈ := func SOME (x∈ ∷ [M])  ∈  Φ
         → αρ-special 
                (αstate {si = si} αen (IF-NONE {ty} {S} {Se}
                                       thn els ;  prg) (o∈ ∷ rVM) sVM Φ)
           ([] , αstate           αen     (els ;∙ prg) (x∈ ∷ rVM) sVM Φ)

  ITER'n : ∀ {αen ty l∈ Φ rS sS iterate prg rVM sVM}
         → l∈ := func (NIL ty) [M]  ∈  Φ
         → αρ-special
               (αstate αen (ITER' {ty} {rS} {sS} iterate ∙ prg)       rVM   (l∈ ∷ sVM) Φ)
           (_ , αstate αen                                 prg        rVM         sVM  Φ)

  ITER'c : ∀ {αen ty l∈ x∈ xs∈ Φ rS sS iterate prg rVM sVM}
         → l∈ := func CONS (x∈ ∷ xs∈ ∷ [M])  ∈  Φ
         → αρ-special
               (αstate αen (ITER' {ty} {rS} {sS} iterate ∙ prg)       rVM   (l∈ ∷ sVM) Φ)
           (_ , αstate αen (iterate ;∙     ITER' iterate ∙ prg) (x∈ ∷ rVM) (xs∈ ∷ sVM) Φ)

  app-bf : ∀ {αen args bt S si prg rVM sVM Φ} {Margs : Match Γ args}
         → {bf : 1-func args (base bt)}
         → (MCargs : MatchConst Φ Margs)
         → αρ-special
                (αstate {si = si} αen (fct {S = S} (D1 bf) ; prg) (Margs +M+ rVM) sVM Φ)
           ([ base bt ] , αstate (wkαE αen) prg (0∈ ∷ (wkM rVM)) (wkM sVM) 
                                     [ 0∈ := const (appD1 bf (getInt MCargs)) // wkΦ Φ ])

-- for convenience when applying several symb. execution steps
_app-αρ-special_-_ : ∀ {Γ ro so αρ Γ` αρ`} ⊎ρ → (ρ∈ : (Γ , αρ) ∈ ⊎ρ)
                   → αρ-special  {Γ} {ro} {so} αρ (Γ` , αρ`)
                   → ⊎Prog-state {ro} {so}
_app-αρ-special_-_ {Γ} {Γ` = Γ`} {αρ`} ⊎ρ ρ∈ sc = ρ∈ ∷= (Γ` ++ Γ , αρ`)

-- here are the special execution steps for αExec-state which enable us to execute
-- the transfer-tokens operation which was impossible with αexec-step
-- αρend[c=s] are concerned with terminating a contract execution when the only variable
-- left on the stack is known to be the expected pair (which will mostly be the case)
-- and αρ-spec executes special program state transitions for contract executions
-- the remaining no-XXX cases deal with some of the possible situations that can arise
-- from processing the list of pending operations (no stands for the new-ops∈ variable
-- that is relevant in all these cases)
-- XXX can be:
--   NIL      if new-ops∈ is NIL
--   ¬sender  if the operation was emitted from an invalid(nonexisting) account
--   ¬p       if the transfered parameter type doesn't match the expected type
--   ¬contr   if the transfer target doesn't exist
--   c≡s      if everything above is NOT the case and the transfer target is the
--               same as the source
--   c≢s      same only that target and source are different; in this case it is assumed
--               that it is still not known whether sender can support the tokens sent
--               and a disjunction on this fact is produced
data ασ-special {Γ} : αExec-state Γ → ⊎Exec-state → Set where

  αρendc=s    : ∀ {αcts₁ αcts₂ p s c=s adr blc∈ amn∈
                   no,ns∈ new-ops∈ new-storage∈ Φ pending}
              → no,ns∈ := func (PAIR {list ops} {s})
                               (new-ops∈ ∷ new-storage∈ ∷ [M])  ∈  Φ
              → ασ-special (αexc αcts₁
                                 (inj₁ (αpr {p = p} {s} c=s c=s
                                            (αstate (αenv αcts₂ adr adr blc∈ amn∈)
                                                    end (no,ns∈ ∷ [M]) [M] Φ)))
                                 pending)
                [ _ , αexc (βset adr (αupdsrg c=s new-storage∈) αcts₁)
                           (inj₂ Φ)
                           (pending ++ [ new-ops∈ , adr ]) ]

  αρend       : ∀ {αcts₁ αcts₂ p s x y curr send cadr sadr blc∈ amn∈
                   no,ns∈ new-ops∈ new-storage∈ Φ pending}
              → no,ns∈ := func PAIR (new-ops∈ ∷ new-storage∈ ∷ [M])  ∈  Φ
              → cadr ≢ sadr
              → ασ-special {Γ} (αexc αcts₁
                                     (inj₁ (αpr {p = p} {s} {x} {y} curr send
                                                (αstate (αenv αcts₂ cadr sadr blc∈ amn∈)
                                                        end (no,ns∈ ∷ [M]) [M] Φ)))
                                     pending)
                [ [ mutez // Γ ]
                , αexc (βset cadr (wkC (αupdate curr blc∈ new-storage∈))
                       (βset sadr (αupdblc (wkC send) 0∈) (wkβ αcts₁)))
                       (inj₂ [ 0∈ := wk⊢ (αContract.balance send ∸ₘ amn∈) // wkΦ Φ ])
                       (wkp pending ++ [ there new-ops∈ , cadr ]) ]

  αρ-spec     : ∀ {αcts p s x y curr send αρ Γ` αρ` pending}
              → αρ-special αρ (Γ` , αρ`)
              → ασ-special {Γ} (αexc αcts
                                     (inj₁ (αpr {p = p} {s} {x} {y} curr send αρ))
                                     pending)
                    [ Γ` ++ Γ , αexc (wkβ αcts)
                                     (inj₁ (αpr (wkC curr) (wkC send) αρ`))
                                     (wkp pending) ]

  no-NIL      : ∀ {αcts new-ops∈ Φ sadr pending}
              → new-ops∈ := func (NIL _) [M]  ∈  Φ
              → ασ-special (αexc αcts (inj₂ Φ) [ new-ops∈ , sadr // pending ])
                      [ _ , αexc αcts (inj₂ Φ) pending ]

  no-¬sender  : ∀ {αcts Φ new-ops∈ sadr pending}
              → αcts sadr ≡ nothing
              → ασ-special (αexc αcts (inj₂ Φ) [ new-ops∈ , sadr // pending ])
                      [ _ , αexc αcts (inj₂ Φ) pending ]

  no-¬p       : ∀ {αcts new-ops∈ op∈ ty P x∈ tok∈ cadr∈ more-ops∈ Φ
                   cadr p s αc sadr x y αs pending}
              → new-ops∈ := func CONS (op∈ ∷ more-ops∈ ∷ [M])  ∈  Φ
              → op∈ := func (TRANSFER-TOKENS {ty} {P}) (x∈ ∷ tok∈ ∷ cadr∈ ∷ [M])  ∈  Φ
              → cadr∈ := contr cadr  ∈  Φ
              → αcts cadr ≡ just (p , s , αc)
              → αcts sadr ≡ just (x , y , αs)
              → ty ≢ p
              → ασ-special (αexc αcts (inj₂ Φ) [  new-ops∈ , sadr // pending ])
                      [ _ , αexc αcts (inj₂ Φ) [ more-ops∈ , sadr // pending ] ]

  no-¬contr   : ∀ {αcts new-ops∈ op∈ p P x∈ tok∈ cadr∈ more-ops∈ Φ
                   cadr sadr x y αs pending}
              → new-ops∈ := func CONS (op∈ ∷ more-ops∈ ∷ [M])  ∈  Φ
              → op∈ := func (TRANSFER-TOKENS {p} {P}) (x∈ ∷ tok∈ ∷ cadr∈ ∷ [M])  ∈  Φ
              → cadr∈ := contr cadr  ∈  Φ
              → αcts cadr ≡ nothing
              → αcts sadr ≡ just (x , y , αs)
              → ασ-special (αexc αcts (inj₂ Φ) [  new-ops∈ , sadr // pending ])
                      [ _ , αexc αcts (inj₂ Φ) [ more-ops∈ , sadr // pending ] ]

  no-c≡s      : ∀ {αcts new-ops∈ op∈ p P x∈ tok∈ cadr∈ more-ops∈ Φ adr s αc pending}
              → new-ops∈ := func CONS (op∈ ∷ more-ops∈ ∷ [M])  ∈  Φ
              → op∈ := func (TRANSFER-TOKENS {p} {P}) (x∈ ∷ tok∈ ∷ cadr∈ ∷ [M])  ∈  Φ
              → cadr∈ := contr adr  ∈  Φ
              → αcts adr ≡ just (p , s , αc)
              → ασ-special {Γ} (αexc αcts (inj₂ Φ) [ new-ops∈ , adr // pending ])
                [ [ mutez / pair p s // Γ ]
                , αexc (wkβ αcts)
                       (inj₁ (αpr (wkC αc) (wkC αc)
                                  (αstate (αenv (wkβ αcts) adr adr
                                                (wk∈ (αContract.balance αc)) 0∈)
                                          (αContract.program αc ;∙ end)
                                          (1∈ ∷ [M]) [M]
                                          [ 0∈ := const 0
                                          / 1∈ := wk⊢ (func PAIR
                                                       (x∈ ∷ αContract.storage αc ∷ [M]))
                                          // wkΦ Φ ]
                                  )))
                       (wkp [ more-ops∈ , adr // pending ]) ]
  no-c≢s      : ∀ {αcts new-ops∈ op∈ p P x∈ tok∈ cadr∈ more-ops∈ Φ
                   cadr s αc sadr x y αs pending}
              → new-ops∈ := func CONS (op∈ ∷ more-ops∈ ∷ [M])  ∈  Φ
              → op∈ := func (TRANSFER-TOKENS {p} {P}) (x∈ ∷ tok∈ ∷ cadr∈ ∷ [M])  ∈  Φ
              → cadr∈ := contr cadr  ∈  Φ
              → αcts cadr ≡ just (p , s , αc)
              → αcts sadr ≡ just (x , y , αs)
              → cadr ≢ sadr
              → ασ-special {Γ} (αexc αcts (inj₂ Φ) [ new-ops∈ , sadr // pending ])
                [ _ , αexc αcts (inj₂ [ αContract.balance αs <ₘ tok∈ // Φ ])
                           [ more-ops∈ , sadr // pending ]
                / [ mutez / pair p s // Γ ]
                , αexc (wkβ αcts)
                       (inj₁ (αpr (wkC αc) (wkC αs)
                                  (αstate (αenv (wkβ αcts) cadr sadr 0∈ (wk∈ tok∈))
                                          (αContract.program αc ;∙ end)
                                          (1∈ ∷ [M]) [M]
                                          [ 0∈ := wk⊢ (func ADDm
                                                  (tok∈ ∷ αContract.balance αc ∷ [M]))
                                          / 1∈ := wk⊢ (func PAIR
                                                  (x∈   ∷ αContract.storage αc ∷ [M]))
                                          // wkΦ [ αContract.balance αs ≥ₘ tok∈ // Φ ] ]
                                  )))
                       (wkp [ more-ops∈ , sadr // pending ]) ]
              
-- more convenience ...
infix  09 _∷[]=_
_∷[]=_ : ∀ {Γ ασ} {⊎σ : ⊎Exec-state} → (Γ , ασ) ∈ ⊎σ → ⊎Exec-state → ⊎Exec-state
here {xs = xs} refl ∷[]= ⊎σ` = ⊎σ` ++ xs
there {x} σ∈ ∷[]= ⊎σ` = [ x // σ∈ ∷[]= ⊎σ` ]

infixl 3 _app-ασ-special_-_ 
_app-ασ-special_-_ : ∀ {Γ ασ ⊎σ`} ⊎σ → (σ∈ : (Γ , ασ) ∈ ⊎σ) → ασ-special {Γ} ασ ⊎σ`
                   → ⊎Exec-state
_app-ασ-special_-_ {⊎σ` = ⊎σ`} ⊎σ σ∈ sc = σ∈ ∷[]= ⊎σ`

