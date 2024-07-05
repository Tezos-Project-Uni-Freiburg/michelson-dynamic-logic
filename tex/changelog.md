## Change Log

### [short] We will emphasize the rationale, explain particular challenges, and compare with the related work on Michelson. (introduction)

See last three paragraphs of the introduction before the contributions.

### [short] Discuss gas, intrinsic typing and its consequences for type preservation (introduction)

Final paragraph of introduction.

### [1 day] We will add a comparison to other symbolic semantics/dynamic logic approaches for bytecode languages. (related work)

We added two new subsections to the related work, discussing work on symbolic execution for bytecode languages (jvm and wasm) and discussing other related uses of dynamic logic. 

### [2 days] Discuss the relation to the original big-step semantics (including Agda proof).

We implemented the big-step semantics and proved the equivalence between the big-step semantics and the small-step formulation used in the paper. We switched the order of sections 3.1 and 3.2 and modified 3.2 to directly refer to this formalized big-step semantics. We state the equivalence of the two semantics in a short new section 3.3. (proofs in the supplementary material) 

### [short] Discuss simple equations with an example (beginning of 4.1)

Added two example equations at the end of section 4.1.

### [short] Clarify the implementation of the modality of the DL in Agda (section 4.2)

Added explicit reference to definition of ProgState.

### [short] Add some examples (throughout)

1. Heterogenous list (l. 250)
2. The interaction of Context, abstract stack, and formulas to represent an abstract state (l.441-454)
3. Illustration of expand and unfold as part of the PUSH instruction (l.555-564)
