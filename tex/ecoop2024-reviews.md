ECOOP 2024 Paper #314 Reviews and Comments
===========================================================================
Paper #314 A Dynamic Logic for Symbolic Execution for the Smart Contract
Programming Language Michelson


Review #314A
===========================================================================

Paper summary
-------------
The paper defines a symbolic semantics for a "representative" core of the Tezos blockchain smart contract language Michelson, based on dynamic logic. The selection of this core set of instructions is included in the contributions, although there is no discussion about why is it "representative" nor a comparison with other "cores".

The symbolic semantics is proved sound with respect a concrete one. Both semantics are instances of a parametric one, setting a framework that eases establishing a relationship between them. This setting is also listed as a contribution.

The setting is implemented in Agda, being thus the soundness proof mechanised, what the authors identify as the "sole goal" of the paper. The code will be submitted as an artefact.

Finally, the authors claim this work proposes "an approach to verification that is based on symbolic execution". However, this claim is not substantiated, since there is no explanation of illustration about how to use the approach developed for verifying Michelson programs (even if there is space, as only 20 pages were used).

I would like to see several questions addressed:
1. About the set of instructions selected: please provide a rationale and compare with other sets, namely that of Mi-Cho-Coq, HELMHOLTZ, and that of the translation to Why3.
2. The main choices were not justified: why symbolic execution, why dynamic logic, and why Agda?
3. There are other symbolic semantics/dynamic logic approaches developed for bytecode (Javascript or Wasm, for instance). How do you compare your setting and results with these works?
4. Your model do not account for gas. However, gas consumption affects liquidity and there are "out-of-gas" vulnerabilities in smart contracts. Don't these issues affect functional correctness?
5. You don't mention a type preservation result for the semantics defined in Figure 1b. Shouldn't it be stated (and proved)?
6. Since the semantics of Michelson is big-step, to better root your small-step semantics, it would be important to show its relationship with the actual Michelson semantics. Do you consider defining a big-step semantics and prove a correspondence with the small-step one?
7. The instruction mpush appears in the "run-time syntax" to allow to push "an arbitrary list of values on the stack". You do not mention its typing rule nor refer to a subject-reduction result. Discuss this issue.
8. Still related with the previous item, in line 294, you state a result "parameterization ensures ... executions well-typed" that I did not find stated (and proved). In lines 314-316, again, it seems you are assuming type preservation.
9. About the comment in lines 357-359: not validating contract addresses may lead to type cast vulnerabilities, as studied by Crafa et al. [1], right?
10. In line 379 you mention, without explaining "simple functions" and then say that arguments must be variables (ruling out, e.g., function calls). Then you say that formulae are restricted to variable equality. Explain the restrictions and how they affect expressiveness.
11. You treat sets as lists (lines 386 and 423). How do you avoid repeated elements (or they are not problematic)?

[1] Silvia Crafa, Matteo Di Pirro, Elena Zucca: Is Solidity Solid Enough? Financial Cryptography Workshops 2019: 138-153

Soundness
---------
4. Strong

Justification and comments on soundness
---------------------------------------
The key soundness result of showing that an abstract step corresponds to a concrete one is proved in Agda. Why have nonetheless a doubt and a suggestion.

The doubt is about a type preservation result from (core) Michelson to Agda terms (for any program) and then about subject-reduction.

The relationship between the big and the small-step semantics would also provide confidence about the applicability of the work to real smart contracts.

Significance
------------
3. Acceptable

Justification and comments on significance
------------------------------------------
The contribution is valid and as a first approach, relevant. However, there are several restrictions not justified and their impact in real programs is not discussed. Moreover, it is difficult to judge the usability and effectiveness of the approach, as no significant examples of smart contracts were used to validate the setting.

Presentation
------------
4. Strong

Justification and comments on presentation
------------------------------------------
The article is well written, with good illustration of the technicalities using simple yet significant examples. Apart from the lack of justification of many choices, the comparison with related work is shallow, listing it but not referring pros and cons nor comparing with the setting the authors defined. This shortcomings do not result from lack of space, as the paper has only 20 pages.

Notice that when you refer to the parameter Mode in the text, you are not using the proper text environment and the word appears to be not well typeset.

Reviewer expertise
------------------
3. Knowledgeable



Review #314B
===========================================================================

Paper summary
-------------
This paper presents a core calculus for the Michelson smart contract language and a formalization of a verification system for Michelson smart contracts that is based on dynamic logic and utilizes symbolic execution for reasoning. The core calculus and verification system are extended to support chained contracts in a transaction and the paper proves the soundness of the verification system for both single contracts and chained contracts. All of the paper’s formal contributions are mechanized/encoded in Agda.

Soundness
---------
3. Acceptable

Justification and comments on soundness
---------------------------------------
I didn’t find any issues with soundness in the paper. But, I am not confident in my assessment because I had a hard time understanding the formalisms in the paper due to their presentation in Agda notation and the paper’s focus on the low-level details of the Agda encoding. Below are some questions I had while reading the paper that are related to soundness.

#### Questions I have related to soundness:
* I’m surprised at the claim that this paper contributes a core calculus for Michelson that covers a representative subset of instructions. Hasn’t this been done before in other work?
* Is init on ln 211 the initial deposit?
* On ln 232 do you mean “else” rather than “thn” on the top of the judgement?
* Where does dynamic logic play a part in your formalized symbolic execution rules?

Significance
------------
2. Weak

Justification and comments on significance
------------------------------------------
Overall, the paper’s presentation does not clearly distinguish its contributions from related work in the space nor provides motivation for the work nor points out technical challenges faced with the formalism outside of challenges faced by encoding everything in Agda. Several aspects of the paper’s significance (that I would expect to be very clear in a research paper meeting the bar for publication at ECOOP) are unclear in this paper:
* Why is dynamic logic a good choice for verifying Michelson smart contracts? I.e. What is the motivation for adapting dynamic logic based verification with symbolic execution reasoning (which has only been applied to Java, an general purpose OOP language) to Michelson (a functional language for smart contracts and the blockchain).
* What challenges and solutions did you come up with when adapting dynamic logic based verification to Michelson smart contracts? Adapting a technique from an OOP to functional domain and to the smart contracts/blockchain domain should have some impact on the formal system and proofs, especially compared to prior work (like the Java work that uses dynamic logic for verification). But, this is not discussed in the paper. The presentation of the paper also doesn’t make clear the novel impact supporting chained contracts has on the formalisms; the solutions for supporting chained contracts presented in the paper appear relatively straightforward.
* Quite a few verification approaches have been applied to Michelson programs, and this paper tries to distinguish itself by providing a symbolic execution-based approach, which has not been done in prior work. Why is symbolic execution-based reasoning a worthwhile technique to apply to Michelson programs?

Presentation
------------
1. Very weak

Justification and comments on presentation
------------------------------------------
In general, the paper does not meet the bar for publication at ECOOP in terms of presentation; the paper reads much more as a tech-report than a research paper. I provide both major and minor suggestions below to raise the paper to an acceptable level for publication.
#### Major suggestions for improvement
* The introduction doesn’t do a great job of motivating the work and should be improved
  * It should explain why a dynamic logic is a good choice for verifying smart contracts in general or for Michelson smart contracts in particular
  * It should explain why other verification frameworks/technique for Michelson fall short and why you want to turn to a symbolic execution approach instead; and then why one based in dynamic logic (see my previous bullet point) is the right choice
* My biggest issue in terms of presentation is that the formalisms are presented in Agda notation making it harder to read and understand the approaches presented. Additionally, due to the Agda notation a lot of time is spent discussing the quirks of the encoding rather than on focusing on the core of the calculus and verification techniques; basically, the presentation in Agda form rather than traditional inference rule form is a distraction and doesn’t add to the paper in a clear way. Rather, it would be better to be traditional in the formal presentation to clarify interesting points in the core calculus and dynamic logic, and have one section dedicated to discussing the Agda encoding and any interesting challenges or contributions there.
  * An example of this issue (and the density of the paper discussed in the next bullet) is that 3.5 pages of the paper are spent on formally presenting the types and program instructions (the syntax of the language) for the Michelson language, which appear relatively straightforward if represented more traditionally.
* The paper is dense with 16 pages of formalism and related text with little to no examples illustrating the ideas. This makes the ideas in the paper hard to follow.
  * For example, Section 2 should show what an example Michelson program looks like and relate it to the formalisms presented so it is easier to understand the modeling choices
  * This example should also describe how Michelson smart contracts/the language works at a high-level and when discussing the example background on related blockchain concepts should be provided for self-containment of the paper

#### Minor suggestions for improvement and typos
* Ln 343: “We add the emitted operations are added to the pending field…” typo

Reviewer expertise
------------------
3. Knowledgeable



Review #314C
===========================================================================

Paper summary
-------------
This paper formalizes an operational semantics for the Michelson smart contract
language. This is a typed, stack-based language for which a big-step operational
semantics is easy to give, but small-step is quite hard. The paper presents a
parameterized semantics that can be instantiated to _both_ a concrete operational
semantics and an "symbolic execution" semantics. The development is formalized in AGDA
and the paper shows how to prove the soundness of the symbolic execution semantics
(by showing it simulates the concrete semantics.)

Soundness
---------
5. Very strong

Justification and comments on soundness
---------------------------------------
The paper delivers very solidly on its promise: a formally verified symbolic execution
for michelson. I also like the tutorial style presentation of the semantics for the
language itself, which I enjoyed reading about.

Significance
------------
3. Acceptable

Justification and comments on significance
------------------------------------------
The paper is a solid and nicely done piece of work, it is great to see a formal semantics
for this language worked out in AGDA and I expect similar methods _may_ be applicable
to other stack-based languages like WASM. On the other hand, there have already been several formal semantics for Michelson e.g.
in Coq or the K framework, and it would be great if the authors could discuss how the AGDA
formalization sheds new light on the semantics of Michelson.

- Do the other formalizations have symbolic execution semantics?
- Do they handle a similar fragment of Michelson?
- In particular, do they handle first-class functions which are currently not handled?

My other concern is that ultimately, we don't actually get a verified
symbolic evaluation engine / verifier for Michelson -- which we do get
with the other approaches. It is nice to get a formal soundness
guarantee for symbolic execution but it would be even better if it was
for the actual implementation. (Ultimately of course, symbolic execution is
unsound as you cannot explore _all_ paths...)

Presentation
------------
5. Very strong

Justification and comments on presentation
------------------------------------------
The paper is very well written -- it tackles a difficult technical problem
and breaks it down nicely, showing the difficulty of formalizing the formalizing
the small step semantics.

Reviewer expertise
------------------
3. Knowledgeable
