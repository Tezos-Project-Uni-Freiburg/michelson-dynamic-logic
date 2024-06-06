# Overview

Thanks to the reviewers for their comments on our submission.

Rev A writes _Moreover, it is difficult to judge the usability and effectiveness of the approach, as no significant examples of smart contracts were used to validate the setting._ This is a misconception, as our correctness proof is not meant to perform symbolic execution in a realistic setting. 
We can run small programs in concrete as well as in abstract, but their execution is very inefficient and does not (is not meant to) scale.

Rev B asks for a rewrite in mathematical notation.
We strongly disagree that mechanized work should be presented using mathematical notation.
We believe that the source code of the proof checker provides an unambigious rendition of the definitions and theorems that were proved. Unlike the mathematical notation, the source code has a clearly defined semantics and (at least in our case) all code included in the paper is directly drawn from the type-checked implementation. Thus, it does not contain errors (not even typos). 
This level of quality wrt soundness is very hard to achieve when manually type setting mathematical notation. 

Also, condensing the discussion of the tool to one section will often render this section incomprehensible. 

# Change List

1. [short] We will emphasize the rationale, explain particular challenges, and compare with the related work on Michelson. (introduction)
2. [1 day] We will add a comparison to other symbolic semantics/dynamic logic approaches for bytecode languages. (related work)
3. [short] Discuss gas, intrinsic typing and its consequences for type preservation (introduction)
4. [2 days] Discuss the relation to the original big-step semantics (including Agda proof).
5. [short] Discuss simple equations with an example (beginning of 4.1)
6. [short] Clarify the implementation of the modality of the DL in Agda (section 4.2)
7. [short] Add some examples (throughout)


# Responses

## Review #314A

I would like to see several questions addressed:

1. About the set of instructions selected: please provide a rationale and compare with other sets, namely that of Mi-Cho-Coq, HELMHOLTZ, and that of the translation to Why3.

        Mi-Cho-Coq, Helmholtz, and the translator are actual verification tools and they support (pretty much) all instructions of the Michelson language as of 2022 (the current version has further datatypes and instructions). As stated in the paper, our goal is to demonstrate the design of a mechanized correctness proof for symbolic execution for Michelson. For that reasons we selected instructions that implement pure functions, stack manipulation instructions, instructions that access blockchain-related components of the state, control flow instructions, and an iteration instruction (this rationale is also part of the introduction). We added more instruction of the same kind to enable showcasing some examples. The implementation and proof of the remaining instructions follows the same, group-specific pattern.

2. The main choices were not justified: why symbolic execution, why dynamic logic, and why Agda?

        Symbolic execution is one of the standard approaches for automatic verification. For simple code it can be used to extract weakest preconditions for failures and normal termination from a program.

        Dynamic logic is used because our goal was to model multi-contract transactions (not possible in the cited work on Helmholtz). We model the blockchain like a heap containing smart contract objects and their state. These objects as well as other state in the blockchain runtime change across transactions. Modeling the Michelson stack is easy in this context. DL is known to be well applicable to OO settings like Java.

        The student who did the initial implementation was reasonably fluent in Agda. 

3. There are other symbolic semantics/dynamic logic approaches developed for bytecode (Javascript or Wasm, for instance). How do you compare your setting and results with these works?

        Thank you for this suggestion. We'll be happy to report this comparison in the revised version.

4. Your model do not account for gas. However, gas consumption affects liquidity and there are "out-of-gas" vulnerabilities in smart contracts. Don't these issues affect functional correctness?

        As far as we understand, Michelson does not suffer from these vulnerabilities. This is (see section 2) because a contract cannot call another contract like a function call. Instead the contract issues a list of operations. This list is processed by the runtime system after the "calling" contract has terminated. There is no "return to the caller"; if gas runs out, the entire suite of contract invocations is rolled back.
		As a contract and its subsidiary contract invocations are either executed in toto or not at all, it's ok to ignore gas in the functional verification. 

5. You don't mention a type preservation result for the semantics defined in Figure 1b. Shouldn't it be stated (and proved)?

        Type preservation follows trivially from the type of the interpreter: Michelson programs are intrinsically typed, so that the interpreter is type preserving by construction. (This also holds for the "real" Michelson implementation.) (Happy to explain that in more detail.)

6. Since the semantics of Michelson is big-step, to better root your small-step semantics, it would be important to show its relationship with the actual Michelson semantics. Do you consider defining a big-step semantics and prove a correspondence with the small-step one?

        We've been thinking of that. We can do it as part of the revision.

7. The instruction mpush appears in the "run-time syntax" to allow to push "an arbitrary list of values on the stack". You do not mention its typing rule nor refer to a subject-reduction result. Discuss this issue.

        This is answered in lines 275-278. mpush is also intrinsically typed, so it's type preserving by construction.

8. Still related with the previous item, in line 294, you state a result "parameterization ensures ... executions well-typed" that I did not find stated (and proved). In lines 314-316, again, it seems you are assuming type preservation.

        Again, this is a consequence of the fact that programs are intrinsically typed: The input stack (i.e., current stack) has type `ri`, the program `prg` transforms an `ri` stack into an `ro` stack. Hence, when the `prg` terminates, intrinsic typing guarantees that the final stack has type `ro`.

9. About the comment in lines 357-359: not validating contract addresses may lead to type cast vulnerabilities, as studied by Crafa et al. [1], right?

        Actually, our implementation (= the Agda proof script) validates all contract addresses before accessing them. The comment says that we could avoid some of that runtime validation, if we added further invariants to our model. For example, the address of the currently running contract as well as the address of its caller are certainly valid, as they were validated when the currently running contract was started. 

10. In line 379 you mention, without explaining "simple functions" and then say that arguments must be variables (ruling out, e.g., function calls). Then you say that formulae are restricted to variable equality. Explain the restrictions and how they affect expressiveness.

        The restriction does not affect expressiveness at all (but simplifies the proofs enormously). Here is why: suppose you want to express `f(x)=x+5`. This equation is not in the expected form. But if we introduce two variables `fx=f(x)` and `y=5`, then the equation is equivalent to `fx=x+y`, which has the desired form. Every function call can be unnested in this way and decomposed into simple equations.
		(simple functions are explained in the next following sentence)

11. You treat sets as lists (lines 386 and 423). How do you avoid repeated elements (or they are not problematic)?

        Repeated elements are not problematic because conjunction and disjunction are both idempotent. Moreover, we are only interested in validity of a formula; our proof does not require any transformation of the formulas.

		
## Review #314B

### Questions I have related to soundness:
* I’m surprised at the claim that this paper contributes a core calculus for Michelson that covers a representative subset of instructions. Hasn’t this been done before in other work?

        Other work (on verification for Michelson) considered all instructions.

* Is init on ln 211 the initial deposit?

        yes, that's what the sentence on 211 says.

* On ln 232 do you mean “else” rather than “thn” on the top of the judgement?

        yes, correct.

* Where does dynamic logic play a part in your formalized symbolic execution rules?

        The DL just provides the theoretical framework. The use of the DL (see section 4.2) is implemented in the type `Abstract ProgState`. (We will make that clearer.)

### Significance

* Why is dynamic logic a good choice for verifying Michelson smart contracts? I.e. What is the motivation for adapting dynamic logic based verification with symbolic execution reasoning (which has only been applied to Java, an general purpose OOP language) to Michelson (a functional language for smart contracts and the blockchain).

        See answer for A.2

* What challenges and solutions did you come up with when adapting dynamic logic based verification to Michelson smart contracts? Adapting a technique from an OOP to functional domain and to the smart contracts/blockchain domain should have some impact on the formal system and proofs, especially compared to prior work (like the Java work that uses dynamic logic for verification). But, this is not discussed in the paper. The presentation of the paper also doesn’t make clear the novel impact supporting chained contracts has on the formalisms; the solutions for supporting chained contracts presented in the paper appear relatively straightforward.

        The challenge is that for supporting chained contracts, we need to model part of the blockchain's runtime system in Agda and perform proofs about it. The DL approach was helpful because it allows us to reason about changing objects (in particular, state component and balance of a contract). Our design enables a modular implementation of the chained proof on top of the single-contract proof.

* Quite a few verification approaches have been applied to Michelson programs, and this paper tries to distinguish itself by providing a symbolic execution-based approach, which has not been done in prior work. Why is symbolic execution-based reasoning a worthwhile technique to apply to Michelson programs?

        See answer A.2. 
		
### Presentation

We are happy to address the comments for improvement (improve the introduction, add and discuss some examples), except the biggest issue (see overview).


We will also *not* talk down on other verification approaches. We believe that an approach based on DL is a viable alternative that has not been explored, yet. 

## Review #314C


* Do the other formalizations have symbolic execution semantics?

        As far as we know, the K-framework has a symbolic execution semantics. The Coq formalization can manage open terms, but only in the context of proof. Helmholtz is a type checker.

* Do they handle a similar fragment of Michelson?

        They are verification tools and handle all instructions available around 2022. 

* In particular, do they handle first-class functions which are currently not handled?

        Yes, they do. And yes, we don't handle first-class functions, yet.

* we don't actually get a verified symbolic evaluation engine

        No, but it's a starting point. To obtain that goal one would have to implement an SE engine in Agda (or Coq), prove it correct, and extract a C implementation with better performance. (Maybe we can get funding for that.)
