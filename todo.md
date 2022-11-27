## current state

### formalizing Michelson:

```agda
data Type : Set where ...
data Inst : Set where ...
data Prog : Set where ...
data tStack : Set where ...
data _⊢_⇒_ : Inst → tStack → tStack → Set where
  ADD   : ∀ {tS}           →  ADD        ⊢     nat ∷ nat ∷ tS   ⇒             nat ∷ tS
  ...
data Contract[p:_s:_prg:_] : Type → Type → Prog → Set where
  typechecked:_ : ∀ {pt st prg}
```

possible problems:
- only typing of instructions formalized, not their semantics
- could be nicer to have one formalization that works on typed terms and then derive everything from it
  ~> kinda like my first attempt, but then i was unhappy with that for some reason?!? ... maybe because it was kinda difficult/ugly to derive the typechecking from that?

### formalizing the DL:

```agda
data Context : Set where ...									context of symbolic terms
data _⊢_   : Context → Type → Set ...								terms, functions
data _⊢Stack : Context → Set ...
data _⊢Fml : Context → Set ...									formulas, predicates
data state : (Γ : Context) → Prog → Γ ⊢Stack → Γ ⊢Stack → Γ ⊢Fml → Set ...			as in paper.pdf
data _→ₛ_ : ∀ {...} → state Γ (inst ; prg) s11 s12 Φ → state Δ prg s21 s22 Ψ → Set ...		state transitions as in paper.pdf
```

possible problems:
- state transitions are defined by relation rather than prooven/derived from Michelson formalization
