
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

open import Data.List.Relation.Unary.Any hiding (map)
open import Data.List.Membership.Propositional using (_∈_)


------------------------- special cases for box transitions -----------------------------

data MatchConst {Γ} (Φ : List (Formula Γ)) : ∀ {S} → Match Γ S → Set where
  [MC] : MatchConst Φ [M]
  _∷_  : ∀ {bt x S M} {v∈ : base bt ∈ Γ} 
       → (v∈ := const x) ∈ Φ →  MatchConst Φ {S} M → MatchConst Φ (v∈ ∷ M)

getInt : ∀ {Γ Φ S M} → MatchConst {Γ} Φ {S} M → Int S
getInt [MC] = [I]
getInt (_∷_ {x = x} v∈:=const MC) = x ∷ (getInt MC)


data αρ-special {Γ ro so} :         αProg-state        Γ  {ro} {so}
                          → ∃[ Γ` ] αProg-state (Γ` ++ Γ) {ro} {so} → Set where

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

  app-bf : ∀ {αen args result S si prg rVM sVM Φ} {Margs : Match Γ args}
         → {bf : 1-func args (base result)}
         → (MCargs : MatchConst Φ Margs)
         → αρ-special
                (αstate {si = si} αen (fct {S = S} (D1 bf) ; prg) (Margs +M+ rVM) sVM Φ)
           ([ base result ] , αstate (wkαE αen) prg (0∈ ∷ (wkM rVM)) (wkM sVM) 
                                     [ 0∈ := const (appD1 bf (getInt MCargs)) // wkΦ Φ ])
         

_app-αρ-special_-_ : ∀ {Γ ro so αρ Γ` αρ`} ⊎ρ → (ρ∈ : (Γ , αρ) ∈ ⊎ρ)
                   → αρ-special  {Γ} {ro} {so} αρ (Γ` , αρ`)
                   → ⊎Prog-state {ro} {so}
_app-αρ-special_-_ {Γ} {Γ` = Γ`} {αρ`} ⊎ρ ρ∈ sc = ρ∈ ∷= (Γ` ++ Γ , αρ`)

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
                [ [ base mutez // Γ ]
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
                [ [ base mutez / pair p s // Γ ]
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
                / [ base mutez / pair p s // Γ ]
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
              
infix  09 _∷[]=_
_∷[]=_ : ∀ {Γ ασ} {⊎σ : ⊎Exec-state} → (Γ , ασ) ∈ ⊎σ → ⊎Exec-state → ⊎Exec-state
here {xs = xs} refl ∷[]= ⊎σ` = ⊎σ` ++ xs
there {x} σ∈ ∷[]= ⊎σ` = [ x // σ∈ ∷[]= ⊎σ` ]

infixl 3 _app-ασ-special_-_ 
_app-ασ-special_-_ : ∀ {Γ ασ ⊎σ`} ⊎σ → (σ∈ : (Γ , ασ) ∈ ⊎σ) → ασ-special {Γ} ασ ⊎σ`
                   → ⊎Exec-state
_app-ασ-special_-_ {⊎σ` = ⊎σ`} ⊎σ σ∈ sc = σ∈ ∷[]= ⊎σ`


{-

------------------------- First Order Logic ---------------------------------------------

getMatch : ∀ {Γ Φ S} → MatchConst {Γ} Φ S → Match Γ S
getMatch [MC] = [M]
getMatch (_∷_ {v∈ = v∈} x MC) = v∈ ∷ (getMatch MC)

setM : ∀ {Γ S} → Match Γ S → Match Γ S → List (Formula Γ)
setM [M] [M] = []
setM (v₁∈ ∷ M₁) (v₂∈ ∷ M₂) = v₁∈ := var v₂∈ ∷ setM M₁ M₂

data FOL⇒ {Γ} : Rel (List (Formula Γ)) 0ℓ where
  app-const-args : ∀ {args result v∈ Φ} {d1f : onedim-func args (base result)}
                 → (MCargs : MatchConst {Γ} Φ args)
                 → (redundant : v∈ := func d1f (getMatch MCargs) ∈ Φ)
                 → FOL⇒ Φ (redundant ∷= v∈ := const (appD1 d1f (getInt MCargs)))
  CAR-PAIR       : ∀ {t1 t2} {v1∈ : t1 ∈ Γ} {v2∈ : t2 ∈ Γ} {p∈ v∈ Φ}
                 →               p∈ := func PAIR (v1∈ ∷ v2∈ ∷ [M])  ∈  Φ
                 → (redundant :  v∈ := func CAR         (p∈ ∷ [M])  ∈  Φ)
                 → FOL⇒ Φ (redundant ∷= v∈ := var v1∈)
  CDR-PAIR       : ∀ {t1 t2} {v1∈ : t1 ∈ Γ} {v2∈ : t2 ∈ Γ} {p∈ v∈ Φ}
                 →               p∈ := func PAIR (v1∈ ∷ v2∈ ∷ [M])  ∈  Φ
                 → (redundant :  v∈ := func CDR         (p∈ ∷ [M])  ∈  Φ)
                 → FOL⇒ Φ (redundant ∷= v∈ := var v2∈)
  replace-VAR    : ∀ {ty u∈ v∈ Φ} {trm : Γ ⊢ ty}
                 →               u∈ := trm     ∈  Φ
                 → (redundant :  v∈ := var u∈  ∈  Φ)
                 → FOL⇒ Φ (redundant ∷= v∈ := trm)
  CONS-NIL       : ∀ {ty v∈ x∈ xs∈ Φ}
                 →               v∈ := func CONS (x∈ ∷ xs∈ ∷ [M])  ∈  Φ
                 →               v∈ := func (NIL ty)         [M]   ∈  Φ
                 → FOL⇒ Φ [ `false ]
  SOME-NONE      : ∀ {ty v∈ x∈ Φ}
                 →               v∈ := func SOME (x∈ ∷ [M])  ∈  Φ
                 →               v∈ := func (NONE ty)  [M]   ∈  Φ
                 → FOL⇒ Φ [ `false ]
  set-args-equal : ∀ {args result v∈ Φ} {d1f : onedim-func args result}
                 → {Margs₁ Margs₂ : Match Γ args}
                 →               v∈ := func d1f Margs₁  ∈  Φ
                 →               v∈ := func d1f Margs₂  ∈  Φ
                 → FOL⇒ Φ (setM Margs₁ Margs₂ ++ Φ)

------------------------- special cases for box transitions -----------------------------

data special-case {Γ αe} : ∀ {stksᵢ stksₒ}
     → Abstract-Box Γ stksᵢ αe → Abstract-Box Γ stksₒ αe → Set where
  CAR    : ∀ {ty₁ ty₂ S ro si so p∈ v₁∈ v₂∈ Φ prg rVM sVM}
         → p∈ := func (PAIR {ty₁} {ty₂}) (v₁∈ ∷ v₂∈ ∷ [M])  ∈  Φ
         → special-case {stksᵢ = stk [ pair ty₁ ty₂ // S ] ro si so}
                        (box (func (D1func CAR) ; prg)  (p∈ ∷ rVM) sVM Φ)
                        (box                      prg  (v₁∈ ∷ rVM) sVM Φ)
  CDR    : ∀ {ty₁ ty₂ S ro si so p∈ v₁∈ v₂∈ Φ prg rVM sVM}
         → p∈ := func (PAIR {ty₁} {ty₂}) (v₁∈ ∷ v₂∈ ∷ [M])  ∈  Φ
         → special-case {stksᵢ = stk [ pair ty₁ ty₂ // S ] ro si so}
                        (box (func (D1func CDR) ; prg)  (p∈ ∷ rVM) sVM Φ)
                        (box                      prg  (v₂∈ ∷ rVM) sVM Φ)
  ITERxs : ∀ {ty sS ri ro so l∈ x∈ xs∈ Φ ip prg rVM sVM}
         → l∈ := func (CONS {ty}) (x∈ ∷ xs∈ ∷ [M])  ∈  Φ
         → special-case {stksᵢ = stk ri ro [ list ty // sS ] so}
                        (box       (ITER' ip ∙ prg)       rVM   (l∈ ∷ sVM) Φ)
                        (box (ip ;∙ ITER' ip ∙ prg) (x∈ ∷ rVM) (xs∈ ∷ sVM) Φ)
  ITER[] : ∀ {ty sS ri ro so l∈ Φ ip prg rVM sVM}
         → l∈ := func (NIL ty) [M]  ∈  Φ
         → special-case {stksᵢ = stk ri ro [ list ty // sS ] so}
                        (box       (ITER' ip ∙ prg)       rVM   (l∈ ∷ sVM) Φ)
                        (box                   prg        rVM         sVM  Φ)
  IF-Nn  : ∀ {ty S Se ro si so o∈ Φ thn els prg rVM sVM}
         → o∈ := func (NONE ty) [M]  ∈  Φ
         → special-case {stksᵢ = stk [ option ty // S ] ro si so}
                        (box (IF-NONE {Se = Se} thn els ;  prg) (o∈ ∷ rVM) sVM Φ)
                        (box                   (thn     ;∙ prg)       rVM  sVM Φ)
  IF-Nj  : ∀ {ty S Se ro si so o∈ x∈ Φ thn els prg rVM sVM}
         → o∈ := func (SOME {ty}) (x∈ ∷ [M])  ∈  Φ
         → special-case {stksᵢ = stk [ option ty // S ] ro si so}
                        (box (IF-NONE {Se = Se} thn els ;  prg) (o∈ ∷ rVM) sVM Φ)
                        (box                       (els ;∙ prg) (x∈ ∷ rVM) sVM Φ)

------------------------- box disjunction and step application --------------------------

ΣBox = Σ Context λ Γ → Σ Stacks λ stks → Σ (Abstract-Env Γ) λ αe → Abstract-Box Γ stks αe

⊎Boxes = List ΣBox

α→ΣBox : ∀ {Γ stks αe} → Abstract-Box Γ stks αe → ΣBox
α→ΣBox {Γ} {stks} {αe} α = Γ , stks , αe , α

ΣBox→α : (β : ΣBox) → Abstract-Box (proj₁ β) (proj₁ (proj₂ β)) (proj₁ (proj₂ (proj₂ β)))
ΣBox→α β = proj₂ (proj₂ (proj₂ β))

infixl 3 _appBxS_ 
infixl 3 _appFOL_-_
infixl 3 _appSBS_-_
infixl 3 _delBox_

_appBxS_ : ∀ {Γ stks αe} {α : Abstract-Box Γ stks αe}
       → (⊎boxes  : ⊎Boxes)
       → (oldbox∈ : α→ΣBox α  ∈  ⊎boxes)
       → ⊎Boxes
_appBxS_ {α = α} ⊎b ob∈ with box-step α
... | inj₁   (_ , _ , _ , α`)   = ob∈ ∷= (α→ΣBox α`)
... | inj₂ ( (_ , _ , _ , α`)
           , (_ , _ , _ , α‶) ) = ob∈ ∷= (α→ΣBox α`) / (α→ΣBox α‶)

_appFOL_-_ : ∀ {Γ stks αe prg rVM sVM Φ Φ`}
       → (⊎boxes  : ⊎Boxes)
       → (oldbox∈ : α→ΣBox (box {Γ} {stks} {αe} prg rVM sVM Φ)  ∈  ⊎boxes)
       → FOL⇒ Φ Φ`
       → ⊎Boxes
_appFOL_-_ {αe = αe} {prg} {rVM} {sVM} {Φ` = Φ`} ⊎b ob∈ fol⇒
  = ob∈ ∷= (α→ΣBox (box {αe = αe} prg rVM sVM Φ`))

_appSBS_-_ : ∀ {Γ αe stksᵢ stksₒ α α`}
       → (⊎boxes  : ⊎Boxes)
       → (oldbox∈ : α→ΣBox α  ∈  ⊎boxes)
       → special-case {Γ} {αe} {stksᵢ} {stksₒ} α α`
       → ⊎Boxes
_appSBS_-_ {α` = α`} ⊎b ob∈ sc = ob∈ ∷= (α→ΣBox α`)

_delBox_ : ∀ {Γ stks αe prg rVM sVM}
       → (⊎boxes  : ⊎Boxes)
       → (badbox∈ : α→ΣBox(box {Γ} {stks} {αe} prg rVM sVM [ `false ])  ∈  ⊎boxes)
       → ⊎Boxes
⊎b delBox bb∈ = del bb∈

-}

