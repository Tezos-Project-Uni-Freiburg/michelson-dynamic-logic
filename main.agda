blubb = 42

module test-tying where
  open import Typing

  ---- simple programs ------------------------------------------------------------------

  simple-01-program  = CDR ; NIL ops ; PAIR ; end
  simple-01-contract : Contract[p: unit
                                s: unit
                              prg: simple-01-program ]
  simple-01-contract = typechecked: CDR f∣ NIL ops f∣ PAIR f∣ id

  simple-02-program  = CAR ; PUSH nat 1 ; ADD ; NIL ops ; PAIR ; end
  simple-02-contract : Contract[p: nat s: nat prg: simple-02-program ]
  simple-02-contract = typechecked: (CAR f∣ PUSH nat 1 f∣ ADD f∣ NIL ops f∣ PAIR f∣ id)

  ---- simple ITER program addElem ------------------------------------------------------

  addElems-program   = CAR ; DIP 1 (PUSH nat 0 ; end) ; ITER (ADD ; end) ; NIL ops ; PAIR ; end
  addElems-contract  : Contract[p: list nat
                                s:      nat
                              prg: addElems-program ]
  addElems-contract  = typechecked: CAR f∣
                                    DIP (list nat ∷ []) refl (PUSH nat 0 f∣ id) s∣
                                    ITER (ADD f∣ id) s∣ NIL ops f∣ PAIR f∣ id

  ---- simple test programs for DIP n and option ----------------------------------------

  test-DIPn-prg1     = NIL unit ; DIP 0 (UNIT ; CONS ; end) ;
                      DIP 1 (CDR ; end) ;
                      PUSH nat 42 ;
                      DIP 2 (PUSH nat 1 ; ADD ; end) ; end
  test-DIPn-prg2     = NIL ops ; PAIR ; end
  test-DIPn-program  = test-DIPn-prg1 ;; DROP 2 ; test-DIPn-prg2

  ⊢test-DIPn-prg1    : test-DIPn-prg1 ⊢ pair unit nat ∷ [] ↠ nat ∷ list unit ∷ nat ∷ []
  ⊢test-DIPn-prg1    = NIL unit f∣ DIP [] refl (UNIT f∣ (CONS f∣ id)) s∣
                      DIP (list unit ∷ []) refl (CDR f∣ id) s∣
                      PUSH nat 42 f∣ DIP (nat ∷ list unit ∷ []) refl (PUSH nat 1 f∣ ADD f∣ id) s∣ id

  ⊢test-DIPn-prg2    : test-DIPn-prg2 ⊢ nat ∷ [] ↠ pair (list ops) nat ∷ []
  ⊢test-DIPn-prg2    = NIL ops f∣ PAIR f∣ id

  ⊢test-DIPn-DROP    : DROP 2 ; end ⊢ nat ∷ list unit ∷ nat ∷ [] ↠ nat ∷ []
  ⊢test-DIPn-DROP    = DROP (nat ∷ list unit ∷ []) refl s∣ id

  test-DIPn-contract : Contract[p: unit
                                s:  nat
                              prg: test-DIPn-program ]
  test-DIPn-contract = typechecked: ⊢test-DIPn-prg1 ;∣ ⊢test-DIPn-DROP ;∣ ⊢test-DIPn-prg2

  test-option-prog   = CAR ; NIL ops ; PAIR ; end
  test-option-cont   : Contract[p: option bool
                                s: option bool
                              prg: test-option-prog ]
  test-option-cont   = typechecked: CAR f∣ NIL ops f∣ PAIR f∣ id

  ---- advanced ITER program sort with nested ITERs -------------------------------------

  sort-inner-if-prg  = IF (DIG 1 ; DIP 1 (CONS ; DIP 1 (NONE nat ; end) ; end) ; end)
                          (SOME ; DUG 2 ; end) ; end
  ⊢sort-inner-if-prg : sort-inner-if-prg ⊢ bool ∷ nat ∷ nat ∷ list nat ∷ []
                                        ↠ nat ∷ list nat ∷ option nat ∷ []
  ⊢sort-inner-if-prg = IF (DIG (nat ∷ []) refl s∣ DIP (nat ∷ []) refl (CONS f∣ DIP (list nat ∷ []) refl (NONE nat f∣ id) s∣ id) s∣ id)
                          (SOME f∣ DUG (nat ∷ list nat ∷ []) refl s∣ id) s∣ id
  sort-if-none-prg   = IF-NONE (DIP 2 (NONE nat ; end) ; end)
                              (DUP 1 ; DUP 3 ; COMPARE ; LT ; sort-inner-if-prg) ; end
  ⊢sort-if-none-prg  : sort-if-none-prg ⊢ option nat ∷ nat ∷ list nat ∷ []
                                        ↠ nat ∷ list nat ∷ option nat ∷ []
  ⊢sort-if-none-prg  = IF-NONE (DIP (nat ∷ list nat ∷ []) refl (NONE nat f∣ id) s∣ id)
                              (DUP [] refl s∣ DUP (nat ∷ nat ∷ []) refl s∣ COMPARE f∣ LT f∣ ⊢sort-inner-if-prg) s∣ id
  sort-iteriter-prg  = ITER (SOME ; DIG 1 ; DIP 1 (NIL nat ; end) ;
                            ITER ( DIG 2 ; sort-if-none-prg ;; CONS ; end) ;
                            DIG 1 ; IF-NONE end (CONS ; end) ;
                            DIP 1 (NIL nat ; end) ; ITER (CONS ; end) ; end) ; end
  ⊢sort-iteriter-prg : sort-iteriter-prg ⊢ list nat ∷ list nat ∷ [] ↠ list nat ∷ []
  ⊢sort-iteriter-prg = ITER (SOME f∣ DIG (option nat ∷ []) refl s∣ DIP (list nat ∷ []) refl (NIL nat f∣ id) s∣
                            ITER (DIG (nat ∷ list nat ∷ []) refl s∣ ⊢sort-if-none-prg ;∣ CONS f∣ id) s∣
                            DIG (list nat ∷ []) refl s∣ IF-NONE id (CONS f∣ id) s∣
                            DIP (list nat ∷ []) refl (NIL nat f∣ id) s∣ ITER (CONS f∣ id) s∣ id) s∣ id

  sort-programm      = CAR ; IF-CONS
                              (DIP 1 (NIL nat ; end) ; CONS ; DIG 1 ; sort-iteriter-prg)
                              (NIL nat ; end) ;
                            NIL ops ; PAIR ; end
  sort-contract      : Contract[p: list nat
                                s: list nat
                              prg: sort-programm ]
  sort-contract      = typechecked: CAR f∣ IF-CONS (DIP (nat ∷ []) refl (NIL nat f∣ id) s∣ CONS f∣ DIG (list nat ∷ []) refl s∣ ⊢sort-iteriter-prg)
                                                  (NIL nat f∣ id) s∣ NIL ops f∣ PAIR f∣ id

  ---------------------------------------------------------------------------------------
  ---- ... other stuff ... --------------------------------------------------------------
  ---------------------------------------------------------------------------------------

{-
-}
open import wop -- hiding (a; b; c) ... just like "using" ;)

module simple-single-step-relation where

  Sin : fullStack
  Sin = (pair nat nat , 41 , 0) ∷ []

  step : ∀ {result inst args} → (fSin : fullStack) → inst f⊢ args ⇒ result → MatchTypes args fSin → fullStack
  step {result} fSin if⊢a⇒r match = (result , apply (impl if⊢a⇒r) match) ∷ unchanged match

  S1 = step Sin  CAR              ((pair nat nat , 41 , 0) ∷ [])
  S2 = step S1  (PUSH nat 1)                                 []
  S3 = step S2   ADD               ((nat , 1) ∷ (nat , 41) ∷ [])
  S4 = step S3  (NIL ops)                                    []
  S5 = step S4   PAIR        ((list ops , []) ∷ (nat , 42) ∷ [])
  _ : S5 ≡ (pair (list ops) nat , [] , 42) ∷ []
  _ = refl

  Sin-test-opt-some : fullStack
  Sin-test-opt-some = (pair (option bool) (option bool) , nothing , just false) ∷ []

  infix  4  _/_↦_
  data _/_↦_ : Inst → fullStack → fullStack → Set where
    functional : ∀ {inst args result fS} {typing : inst f⊢ args ⇒ result} {match : MatchTypes args fS}
                →    inst    /    fS  ↦  (result , apply (impl typing) match) ∷ unchanged match

  s1 : CAR / Sin ↦ S1
  s1 = functional {typing = CAR}{match = (pair nat nat , 41 , 0) ∷ []}

--module idee-partielle-step-funktion-mit-parition where

