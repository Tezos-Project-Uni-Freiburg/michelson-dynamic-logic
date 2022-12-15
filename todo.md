# current state

## formalizing Michelson:

```agda
data Type   : Set where ...
data Inst   : Set where ...
data Prog   : Set where ...
data tStack : Set where ...
data _⊢_⇒_  : Inst → tStack → tStack → Set where
  ADD   : ∀ {tS}           →  ADD        ⊢     nat ∷ nat ∷ tS   ⇒             nat ∷ tS
  ...
data Contract[p:_s:_prg:_] : Type → Type → Prog → Set where
  typechecked:_ : ∀ {pt st prg}
```

### possible problems:
- only typing of instructions formalized, not their semantics
- could be nicer to have one formalization that works on typed terms and then derive everything from it
  ~> kinda like my first attempt, but then i was unhappy with that for some reason?!? ... maybe because it was kinda difficult/ugly to derive the typechecking from that?

## formalizing the DL:

```agda
data Context : Set where ...									context of symbolic terms
data _⊢_   : Context → Type → Set ...								terms, functions
data _⊢Stack : Context → Set ...
data _⊢Fml : Context → Set ...									formulas, predicates
data state : (Γ : Context) → Prog → Γ ⊢Stack → Γ ⊢Stack → Γ ⊢Fml → Set ...			as in paper.pdf
data _→ₛ_ : ∀ {...} → state Γ (inst ; prg) s11 s12 Φ → state Δ prg s21 s22 Ψ → Set ...		state transitions as in paper.pdf
```

### possible problems:
- state transitions are defined by relation rather than prooven/derived from Michelson formalization

# topics Dec 14th:

## formalizing Michelson:

- tried a formalization that combines typing and semantics:
  ```agda
  Stack = List (Σ Type ⟦_⟧)

  data _/_⇒_ : Inst → Stack → Stack → Set where
    ADDₙₙ : ∀ {S n m}         →  ADD         /        (nat , n) ∷ (nat , m) ∷ S   ⇒               (nat , n + m) ∷ S
  ```
  => problem is, it won't typecheck automatically and complains about missing ... stuff (the yellow marks, dependencies??)
  - [ ] can i make some clever better use of agda here so it won't complain and hopefully even typecheck automatically?
  - [x] or is this even really important, should i maybe give typing and semantics separately as it is given in the MicRef?
    => automatisches typechecking ist eine gute Sache. Was die bestmoegliche Implementation ist, ist noch nicht klar.

## formalizing the DL:

- i'm still unceirtain about this ...
  - example in JavaDL chapter from book:
   	x≐0 ⇀ ⟨x++⟩(x≐1)	when started in a state where x=0, the program fragment x++ will terminate in a state where x=1
  - so for Michelson this could be something like:
    par≐41 ⇀ ⟨simple02⟩(stor≐42)
  - or in the notation given in the paper:
    {nat;nat} [ simple02 , (Pair par stor) ∷ [] , [] , ∅ ] —→ₛ {nat} [ end , (Pair {} par+1) ∷ [] , [] , ∅ ]
	- [x] is that the overall goal?
	  => kinda: im Prinzip schon, nur das die abstrakten Stacks nur aus Variablen bestehen, und dazu dann Gleichungen die diese mit werten versorgen
  - Ihre mail vom 2.Dez:
    - [x] was sind "MState" / "Maybe MState" ?? Ein oder mehrere konkrete Stacks (also aus type/value Paaren)?
	  => ein paar aus Stacks (MAP beispielsweise braucht auch fuer die konkrete Ausfuehrung einen "shadow" stack)
	- [x] Box-Operator = (List Instr, Stack, Stack) ... also die system states aus Def1 Ihres papers minus dem Predicate?!
	- `models : MState → Formula → Set` sagt, ob ein konkreter Zustand durch eine Formel mit Boxen interpretiert wird
	  - [x] also enthalten Formulas diese Boxen
  
# little questions to keep track of

- [x] can you push a pair? in my current understanding, you can only create pairs from values on the stack, and this has an impact on how we would implement push of course:
  => yes you can push pairs, MichRef says pair is pushable
- [x] so we can try to implement this
  ```agda
  ⟦_⟧ : Type → Set
  ⟦ T ⟧ = {!!}

  -- btw a better type for the PUSH instruction
  postulate
    push : ∀ ty → ⟦ ty ⟧ → Inst
  ```
- [x] PTs comments in simple.agda:
  use a list of type `List (Σ Type ⟦_⟧)` for the stack [...], then the notation will be a bit more involved, but it will be easier to manipulate values in Agda.

# next steps

- [ ] Formeln mit Box-Operator
- [ ] models
- [ ] konkrete und abstrakte steps
- [ ] Benennung ueberdenken! ;P

# reusability

Es waere schoen, wenn man die Definition der Instruktionen fuer die abstrakte Ausfuehrung wiederverwenden koennte
... aber das wird evtl tricky, dann muesste man wahrscheinlich die Instruktionen irgendwie unabhaengig vom Stack definieren?!?!?

- [ ] koennte man eventuell die Instruktionen parametrisiert mit der Anzahl ihrer Argumente definieren?
  dann waere die konkrete und abstrakte Semantik gegeben durch diese Anzahl an Stackelementen
  und in Gleichungen kann man sie dann auch hinschreiben mit der entsprechenden Anzahl an Variablen.
- [ ] angenommen ich habe fuer jede Instruction eine Typing rule:
  ```agda
  data _⊢_⇒_ : Inst → List Type → Type → Set where
	ADD   :                        ADD         ⊢      nat ∷ nat ∷ []  ⇒           nat
  ```
  und eine Semantic rule, zB       ADD         /        n ∷   m ∷ []  ⇒           n+m
  Dann koennte die DL Terme der Form var, const und InstOp haben (und evtl weitere), letztere abgeleitet aus den Regeln von oben
  ... irgendwie dachte ich diese Aussage wuerde konkreter werden :D
- [ ] kann und soll ich evtl sogar das Konzept von Listen mit gegebener Laenge versuchen, wieder zu verwenden (das Hannes in der 2./3. Uebung vorgestellt hat?)
