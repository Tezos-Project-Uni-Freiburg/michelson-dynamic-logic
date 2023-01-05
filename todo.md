# current state of affairs

## Michelson

### relational

#### Typing

- geht ohne die "rekursiven Voraussetzungen zu expanden", es reicht wenn man deren typing checkt
- aktuell leider haesslich und nicht mehr automatisch, aber das laesst sich vielleicht mit ```to/fromWitness``` wieder einrenken
- wie wichtig ist es eigentlich fuer die DL?
  ... vermutlich schon mindestens very nice to have, allerspaetestens wenn ich ganze contracts symbolisch ausfuehren will und, wofuer well typed das Minimum ist.
  
#### Semantics

aktuell existieren nur Experimente in der main mit den funktionalen Instructions

'Strukturelle' Instructions koennte man weiter gliedern in:
- Stack-reorganisierende Instructions; evtl kann man diese sogar wie funktionale darstellen, wenn man das 'funktionale' um Funktionen mit ganzen Stacks als Ergebnis erweitert
- Subprogram Instructions wie ITER, MAP, DIP die auf jeden Fall den Shadow Stack benoetigen.
  - fuer diese benoetigt man nicht nur den Shadow-Stack, sondern auch Shadow-Instructionen fuer Expansion der Rekursion (wobei das wahrscheinlich nicht fuer DIP?!)

### mit partiellen Funktionen

experimentelles Chaos unter partial-everything ...

Ausfuehrung des Typechecking ist jetzt nur noch ein Funktionsaufruf! :smiley:

Programm-Ausfuehrung koennte genauso einfach gehen (evtl mit zusaetzlichem Parameter Gas)

noch unklar:

### Type preservation

... mache ich mal kurz zum eigenen Heading, weil ich da definitiv noch einige Verstaendnis-Sachen fuer mich klaeren muss:
- [ ] grundsaetzlich, was brauche ich denn dafuer, in diesem konkreten Kontext einer "echten" Programmiersprache
  (im Gegensatz zu den minimalistischen und theorie-fokusierten Vorlesungsbeispielen)
  - [ ] welche Postulates koennten das gut ausdruecken?
- ich habe Michelson bislang so versucht zu formalisieren, dass die Eingabe eines Programms in Agda moeglichst aehnlich ist wie eine Eingabe in die vorhandenen Online-Interpreter;
  in der Form sind die Programme definitiv nicht intrinsisch typisierbar, ich kann auch bei den Online Interpretern ungueltige Programme eingeben;
  daher die Fragen:
  - [ ] ist eine intrinsisch getypte Formalisierung ueberhaupt moeglich?? (ich vermute sehr stark nicht, Beispiel ```ADD``` ...)
  - [ ] ist meine erste, relationale Formalisierung besser geeignet, um preservation zu zeigen (klang beim letzten Meeting bei PT ein bisschen so, vielleicht auch ein Missverstaendnis)
  - [ ] ist meine relationale Darstellung von funktionaler Stack-execution (`impl` und `step` mit `f⊢` als Argument, so schick es sein mag, ueberhaupt praktisch anwendbar,
	immerhin benoetigen sie als Argument eine Typing Relation und nicht bloss die Instruction ... **aber vielleicht steckt genau darin der Schluessel zum intrinsischen Typing!!!!!!!!**
- [ ] *aus meinen "stuff to keep in mind"s*:  
  Instructions sind nicht eindeutig getyped, aber Contracts scheinen es zu sein.  
  Aber kann ein Fall auftreten mit Optionalen Datentypen, wo ein ADD je nach Verlauf unterschiedlich getyped waere, und waere das ein Problem?  
  ~> vermutlich heisst die Antwort nein, weil optionale Datentypen (auch `option`, aber ich dachte in erster Linie an `or`) ja immer dekonstruiert werden,
  in diesen Faellen mit entsprechend `IF_xxx` ...

## Dynamic Logic

... still faaaar far away :( ...

paar Grundlegende Ideen die schon klar sind, aber einfach mal zum festhalten:
- die Stacks werden nur noch Variablen enthalten
- die Formeln werden Gleichungen der Form ```var = impl args``` oder ```var = const``` enthalten
- der symbolic state ist die Disjunktion von mehreren "Boxen" aus den beiden Stacks und Formeln
 
# questions and stuff to keep in mind

- [x] step als partielle Funktion; diese koennte mein ```partition``` Experiment in der main verwenden
- [ ] kann und soll ich evtl sogar das Konzept von Listen mit gegebener Laenge versuchen, wieder zu verwenden (das Hannes in der 2./3. Uebung vorgestellt hat?)  
  das koennte vielleicht hilfreich sein beim typechecken von instructions wie DIP wo die laenge des Stacks relevant ist.
- [x] reusability:  
  Es waere schoen, wenn man die Definition der Instruktionen fuer die abstrakte Ausfuehrung wiederverwenden koennte.
- [ ] aktuell ist das typing etwas unschoen und vor allem aufwaendig, aber das laesst sich vielleicht mit ```to/fromWitness``` wieder einrenken

## backup (those ideas probably no longer neeeded ;)

- [ ] can we give a MF by definition (rather than by relating Inst to typing etc) that would still typecheck
  by adjusting our type for the Contract datatype? (siehe auch backup/ALL-...)
  ... and would that have other advantages over relational formalization?

# next steps

Das grosse Ziel:
- [ ] actual step
  - [x] shadow stack semantics fuer ITER
  - [ ] semantics fuer DIP n
	- [ ] im fall von partiellen Funktionen Stacklaengenparameter n fuer diverse Befehle evtl doch expanden?
  - [ ] kleines ITER-testprogramm durch-steppen
- [ ] preservation
  - [ ] Grundlagen refreshen: was will ich eigentlich zeigen?
  - [ ] dies dann in geeignete Postulates giessen und auf die todo-later Liste setzen
  - [ ] ist die relationale Formalisierung ein moeglicher Weg zu intrinsischem Typing?!?!?!?!?!
- [ ] models
- [ ] abstract step
- [ ] SOUNDNESS

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

- [x] which route to take?
  1. Eventuell die "stumpfe" Umsetzung als Referenz + Fallback und dann schauen, ob der "elegante" Ansatz machbar ist?
  2. Oder direkt auf die vollen gehen, man kann ja immer zurueck fallen auf "stumpf"
  ==> eher 2 ...
- [x] fuer den Eleganten Ansatz wuerde sich ein Agda crashkurs fuer mich sehr lohnen: Haben Sie Empfehlungen (online-Tutorials/Buecher der TF)?
  Aaron Stump
- [x] darf ich Sie Mittwochs bis auf weiteres Blockieren bei calendly?

## Jan 4th

Ergebnisse:
- Preservation beachten
- partial functions sind ein bisschen vielversprechender fuer baldige Resultate, auch wenn ```impl : ∀ {inst args result} →   inst f⊢ args ⇒ result  →  ⟦ args ⇒ result ⟧```
  und das anschliessende ```step : ∀ {inst args result} →   inst f⊢ args ⇒ result → fullStack → Match fullStack args  →  ⟦ result ⟧``` sehr elegant sind :smiley:

# dev log

## Michelson

Es gibt verschiedene Ansaetze:

- Instructions: definieren Typing&/Semantics VS sind in Relation zu Typing&/Semantics
- Typing&Semantics: separat oder zusammen definiert

Formalizing the instructions by definitions is at least really bad for pretty program writing, but wheather that's an important criteria is debatable:

Aktuell vielversprechendster Ansatz:
- Typing in Relation zu Inst data set
- Semantics als Funktion der Typing rules

Hauptgrund fuer diesen Ansatz: Es gibt gelegentlich unterschiedliche Typing rules fuer eine Michelson Instruction;  
wuerden wir die Instructions durch ihr Typing definieren, braeuchten wir verschiedene Repraesentationen fuer eine einzige Michelson Instruction.

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

## Dynamic Logic

old state before last meeting

```agda
data Context : Set where ...									context of symbolic terms
data _⊢_   : Context → Type → Set ...								terms, functions
data _⊢Stack : Context → Set ...
data _⊢Fml : Context → Set ...									formulas, predicates
data state : (Γ : Context) → Prog → Γ ⊢Stack → Γ ⊢Stack → Γ ⊢Fml → Set ...			as in paper.pdf
data _→ₛ_ : ∀ {...} → state Γ (inst ; prg) s11 s12 Φ → state Δ prg s21 s22 Ψ → Set ...		state transitions as in paper.pdf
```
