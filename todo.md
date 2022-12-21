# current state

## files

### backup files probably deleted soon ;)

- main-wop.agda
  - [ ] first approach towards DL may be good starting point
  - [ ] main.agda ... currently unused ...

### useful stuff :D

- michelson-separate-minimal.agda 
  - only MF that typechecks contracts fully automatical!
  - typing ```data _⊢_⇒_ : Inst → List Type → Type → Set where```
  - semantics ```_/impl : ∀ {inst args result} →   inst ⊢ args ⇒ result  →  ⟦ args ⇒ result ⟧```
- michelson-singledef-minimal.agda
  backup of different MF versions with different problems
  ```agda
  ⊢Args = List (Σ Type ⟦_⟧)
  data Inst : ⊢Args → (Σ Type ⟦_⟧) → Set where
  ```
  ```agda
  data Inst : (args : List Type) → (result : Type) → ⟦ args ⇒ result ⟧ →  Set where
  ```
  ```agda
  data _⊢_⇒_/_ : Inst → (args : List Type) → (result : Type) → ⟦ args ⇒ result ⟧ →  Set where
  ```

## formalizing Michelson

see useful files for used data structures ...

Es gibt verschiedene Ansaetze:

- Instructions: definieren Typing&/Semantics VS sind in Relation zu Typing&/Semantics
- Typing&Semantics: separat oder zusammen definiert

Aktuell vielversprechendster Ansatz:
- Typing in Relation zu Inst data set
- Semantics als Funktion der Typing rules

Hauptgrund fuer diesen Ansatz: Es gibt gelegentlich unterschiedliche Typing rules fuer eine Michelson Instruction;  
wuerden wir die Instructions durch ihr Typing definieren, braeuchten wir verschiedene Repraesentationen fuer eine einzige Michelson Instruction.

Formalizing the instructions by definitions is at least really bad for pretty program writing, but wheather that's an important criteria is debatable:
- it is currently the only way to give me fully automatic typechecking of Michelson Programs
- [ ] but maybe that can be accomplished with a slightly different type for Contracts

giving the MF as in `michelson-separate-minimal` allows fully automatic typechecking, so it seems to be the most promising so far.

***UPDATE***

some big flaws in typing:
```agda
data _⊢_⇒_ : Inst → List Type → Type → Set where
```
- may not work for `MAP` and similar instructions
- it will also not work for some very easy instructions like `DUP`!!!!!  
  basically any instruction that results in not just one sigle new value
  
Aber vielleicht kann die Darstellung von 'komplizierten' Befehlen mithilfe mehrerer 'einfacher' Befehle nicht nur
Instructions wie ```DIP n``` ueberfluessig machen (```DIP n ≡ PAIR n ; DIP``` und ```PAIR n ≡ PAIR ; ... ; PAIR {n times}```),
sondern auch die Darstellung von: ```DUP ≡ DUP_pair ; UNPAIR``` ...
ne, damit verschiebt man nur die Problematik :D ...  
***einzige Chance:*** dass man hier den shadow Stack nutzt und fuer den in der Semantic Freiheiten zulaesst, die bei
reinen Mainstack-Instructions nicht erlaubt sind, und dafuer erhaellt man dann Mainstack-Instructions wie ADD,
deren Implementierung man direkt fuer die symbolic execution wiederverwerten kann.

## formalizing the DL

old state before last meeting

```agda
data Context : Set where ...									context of symbolic terms
data _⊢_   : Context → Type → Set ...								terms, functions
data _⊢Stack : Context → Set ...
data _⊢Fml : Context → Set ...									formulas, predicates
data state : (Γ : Context) → Prog → Γ ⊢Stack → Γ ⊢Stack → Γ ⊢Fml → Set ...			as in paper.pdf
data _→ₛ_ : ∀ {...} → state Γ (inst ; prg) s11 s12 Φ → state Δ prg s21 s22 Ψ → Set ...		state transitions as in paper.pdf
```

# questions to keep track of

- [ ] can we give a MF by definition (rather than by relating Inst to typing etc) that would still typecheck
  by adjusting our type for the Contract datatype?
  ... and would that have other advantages over relational formalization?
- [x] Instructions like DIP DUP and others can't be formalized with the current approach!!
  ... vielleicht brauche ich doch den stack of type value pairs approach?!
- [ ] Instructions sind nicht eindeutig getyped, aber Contracts scheinen es zu sein.
  Aber kann ein Fall auftreten mit Optionalen Datentypen, wo ein ADD je nach Verlauf unterschiedlich getyped waere, und waere das ein Problem?

# next steps

Das grosse Ziel:
- [ ] actual step
- [ ] models
- [ ] abstract step
- [ ] SOUNDNESS

das klingt irgendwie am einfachsten mit type-value stacks umsetzbar

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

# meetings

## Dec 14th

### formalizing Michelson

- tried a formalization that combines typing and semantics:
  ```agda
  Stack = List (Σ Type ⟦_⟧)

  data _/_⇒_ : Inst → Stack → Stack → Set where
    ADDₙₙ : ∀ {S n m}         →  ADD         /        (nat , n) ∷ (nat , m) ∷ S   ⇒               (nat , n + m) ∷ S
  ```
  => problem is, it won't typecheck automatically and complains about missing ... stuff (the yellow marks, dependencies??)
  - [x] can i make some clever better use of agda here so it won't complain and hopefully even typecheck automatically?
	=> will discuss in Agda AG
  - [x] or is this even really important, should i maybe give typing and semantics separately as it is given in the MicRef?
    => automatisches typechecking ist eine gute Sache. Was die bestmoegliche Implementation ist, ist noch nicht klar.

### formalizing the DL

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


## Dec 21th

### MF (Michelson Formalization)

Aktuell sehe ich zwei moegliche Richtungen:

1. "stumpfe" Umsetzung sehr nah an der gegebenen Michelson Reference, allerdings die Typing Rules und Semantics in eine Relation gefasst:

   ```agda
   data _⊢_↦_ : Inst → fullStack → fullStack → Set where
     ADD   : ∀ {n m fS}          →  ADD  ⊢  (nat , n) ∷ (nat , m) ∷ fS  ↦  (nat , n + m) ∷ fS
   ```

   **PRO**

   - einfache Umsetzung aller moeglichen Michelson Instructions
   - *future proof* fuer moegliche Weiterentwicklung von Michelson

   **CONTRA**

   - Wiederverwendung der Semantischen Regeln fuer Symbolic Execution nicht moeglich
   - viel stumpfe Handarbeit anstelle von systematisierter Charakterisierung verschiedener *Michelson Instruction Classes*
	 durch elegante ***Alternative:***

2. Darstellung mit *funktionalen* Instructions:
   ```agda
   data _⊢_⇒_ : Inst → List Type → Type → Set where
	 ADD   :                            ADD         ⊢      nat ∷ nat ∷ []  ⇒           nat

   ⟦_⇒_⟧ : List Type → Type → Set
   ⟦     [] ⇒ T ⟧ =              ⟦ T ⟧
   ⟦ A ∷ LT ⇒ T ⟧ = ⟦ A ⟧ → ⟦ LT ⇒ T ⟧
   
   _/impl : ∀ {inst args result} →   inst ⊢ args ⇒ result  →  ⟦ args ⇒ result ⟧
   ADD       /impl = _+_
   
   -- noch zu entwickeln:

   _/_↦_ : Inst → (fullStack → fullStack → Set)
   _/_↦_ ADD = ∀ {n m fS}    →    ADD / (nat , n) ∷ (nat , m) ∷ fS ↦ (nat , (ADD /impl) n m) ∷ fS
   -- bzw irgendwie noch eleganter (man darf ja wohl noch traeumen ;)
   ∀ {...} inst / argsTV ∷ fS ↦ (result , (i⊢a⇒r /impl) argsV) ∷ fS
   ```
   
   ... und *strukturellen* Instructions mithilfe von:
   1. Aufspaltung "komplizierter" in einfachere Instruction chains
   2. Einfuehrung des "shadow stacks", den wir ja sowieso brauchen werden
   ```adga
   DIP n inst ≡ transfer2shadow n ; inst ; transfer2main n
   DUP        ≡ DUP2shadow ; transfer2main
   MAP ...
   ```

   **PRO**

   - Wiederverwendbarkeit der "funktionalen" Semantik
   - den Shadow Stack brauchen wir ja sowieso
   - Strukurierung macht die Arbeit evtl 'eleganter' und so wertvoller

   **CONTRA**
   
   - AGDA overkill
   - Erfolg deshalb fraglich
   - bei erheblicher Weiterentwicklung von Michelson evtl nicht future proof bzw groesserer Erweiterungs-Aufwand
   
---

- [ ] which route to take?
  1. Eventuell die "stumpfe" Umsetzung als Referenz + Fallback und dann schauen, ob der "elegante" Ansatz machbar ist?
  2. Oder direkt auf die vollen gehen, man kann ja immer zurueck fallen auf "stumpf"
- [ ] fuer den Eleganten Ansatz wuerde sich ein Agda crashkurs fuer mich sehr lohnen: Haben Sie Empfehlungen (online-Tutorials/Buecher der TF)?
- [ ] darf ich Sie Mittwochs bis auf weiteres Blockieren bei calendly?
