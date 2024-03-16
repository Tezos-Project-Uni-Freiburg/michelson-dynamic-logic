
module 03-2-concrete-execution where

import 00-All-Utilities as H
open import 01-Types
open import 02-Functions-Interpretations

open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary

open import Data.Nat renaming (_≟_ to _≟ₙ_)
open import Data.List.Base hiding ([_]; head; tail)
open import Data.List.Relation.Unary.All using (All; _∷_; []; head; tail)
open import Data.Maybe.Base hiding (map)
open import Data.Product hiding (map)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤;tt)

--! Concrete >

variable
  p s : Type

--! MODE
record MODE : Set₁ where
  field
    𝓜  : Type → Set
    𝓕  : Set

open MODE

--! CMode
CMode : MODE
CMode = record { 𝓜 = ⟦_⟧ ; 𝓕 = ⊤ }

Concrete : ∀ {a}{A : Set a} → (MODE → A) → A
Concrete F = F CMode

------------------------- Execution states and program execution ------------------------

-- contracts are parameterized by their parameter and storage types,
-- they provide evidence that these types are appropriate,
-- as well as their BALANCE and STORAGE (values) and a well typed program (NO shadow prog)
--! Contract
record Contract (Mode : MODE) (p s : Type) : Set where
  constructor ctr
  field
    Param    : Passable p
    Store    : Storable s
    balance  : 𝓜 Mode mutez
    storage  : 𝓜 Mode s
    program  : Program [ pair p s ] [ pair (list operation) s ]

variable Mode : MODE

CContract : Type → Type → Set
CContract = Concrete Contract

--! Account
Account : Mutez → Contract CMode unit unit
Account init = ctr unit unit init tt (`CDR ; `NIL operation ; `PAIR ; end)

-- for updating contracts when their execution terminated successfully
update : Contract Mode p s → 𝓜 Mode mutez → 𝓜 Mode s → Contract Mode p s
update c blc srg = record c{ balance = blc ; storage = srg }
updsrg : Contract Mode p s → 𝓜 Mode s → Contract Mode p s
updsrg c     srg = record c{ storage = srg }
updblc : Contract Mode p s → 𝓜 Mode mutez → Contract Mode p s
updblc c blc     = record c{ balance = blc }
subamn : CContract p s → ⟦ mutez ⟧ → CContract p s
subamn c amn     = record c{ balance = Contract.balance c ∸ amn }

-- the blockchain maps any address to a contract if it stores one at that address
--! Blockchain
Blockchain : (Mode : MODE) → Set
Blockchain Mode = ⟦ addr ⟧ → Maybe (∃[ p ] ∃[ s ] Contract Mode p s)

CBlockchain : Set
CBlockchain = Concrete Blockchain

-- to set an address to a contract on a Blockchain
set : ⟦ addr ⟧ → Contract Mode p s → Blockchain Mode → Blockchain Mode
set adr c bl a
  with a ≟ₙ adr
... | yes refl = just (_ , _ , c)
... | no  ¬adr = bl a

-- empty Blockchain
∅ : Blockchain Mode
∅ adr = nothing

-- this is the environment record that holds the informations necessary to execute
-- env-func instructions
-- it can easily be extended to enable more such instructions
-- the fields self and sender are currently not used for instructions but for
-- handling multi-contract executions where execution results are written back to
-- the blockchain and emitted operations can be executed in the same run
--! Environment
record Environment (Mode : MODE) : Set where
  constructor env
  field
    accounts  : Blockchain Mode
    self      : ⟦ addr ⟧
    sender    : ⟦ addr ⟧
    balance   : (𝓜 Mode) mutez
    amount    : (𝓜 Mode) mutez

CEnvironment : Set
CEnvironment = Concrete Environment

-- PJT: why is balance needed if we can take it from self?

-- this is the program state used to execute any possible Michelson Program on
-- well typed stacks
-- parameterization with the expected output Stacks ensures that the execution
-- model and also the results from contract executions are well typed
-- (meaning they preserve the expected output Stacks)
-- the current stacks are Int's, i.e. typed stacks of values
-- some instructions are expanded to programs that include shadow instructions
--! ProgState
record ProgState (Mode : MODE) (ro so : Stack) : Set where
  constructor state
  field
    {ri si}  : Stack
    en       : Environment Mode
    prg      : ShadowProg ri si  ro so
    rSI      : All (𝓜 Mode) ri
    sSI      : All (𝓜 Mode) si
    Φ        : 𝓕 Mode

open ProgState

Prog-state = ProgState

-- abstract: Φ ∧ < en | rsi , ssi | prg >
pattern _∧<_∣_,_∣_> Φ en rsi ssi prg = state en prg rsi ssi Φ
-- concrete:
pattern <_∣_,_∣_> en rsi ssi prg = state en prg rsi ssi tt
pattern cstate en rsi ssi prg = state en prg rsi ssi tt

CProgState : Stack → Stack → Set
CProgState = Concrete ProgState

CProg-State = CProgState

variable
  ro so : Stack

-- when not executing a single program but entire contracts and blockchain operations
-- this record encapsulates a ProgState that is parameterized with the typing
-- restrictions for the 'self' contract that is executed
-- the sender is the account that triggered the current contract execution
-- it may be the same as self, and their addersses are saved in the Environment
-- of the ProgState
-- they are saved in Prg-running because it was easier to implement
-- the update of a successfully terminated contract execution
-- by updating these contracts and saving them back to the blockchain (i.e. setting
-- their addresses on the blockchain to the updated contracts)
-- it could be possible that instead of saving the contract one could save something
-- like Exec-state.accounts current-address ≡ just (p , s , Contract p s)
-- but it is probably a lot harder and i couldn't see any benefit in doing so
--! PrgRunning
record PrgRunning (Mode : MODE) : Set where
  constructor pr
  field
    {pp ss x y}  : Type
    self         : Contract Mode pp ss
    sender       : Contract Mode x y
    ρ            : ProgState Mode [ pair (list operation) ss ] []

CPrgRunning : Set
CPrgRunning = Concrete PrgRunning

Prg-running = PrgRunning
CPrg-running = CPrgRunning

-- this is the execution state used to execute entire contracts and blockchain operations
-- when it's in a state where a contract is under execution, MPstate will have a value
-- just prg-running containing an approrpiate and well typed ProgState
-- otherwise MPstate having the value nothing signals the execution model to handle
-- the next pending operation
-- those are saved as lists of pairs of lists since every contract emits a
-- (possibly empty) list of operations, the address of the emitter will be saved with it.
--! Transaction
record Transaction (Mode : MODE) : Set where
  constructor _,_
  field
    pops     : (𝓜 Mode) (list operation)
    psender  : ⟦ addr ⟧

CTransaction : Set
CTransaction = Concrete Transaction

--! ExecState
record ExecState (Mode : MODE) : Set where
  constructor exc
  field
    accounts  : Blockchain Mode
    MPstate   : PrgRunning Mode ⊎ 𝓕 Mode
    pending   : List (Transaction Mode)

CExecState : Set
CExecState = Concrete ExecState

Exec-state = ExecState
CExec-state = CExecState

-- these are all the preliminary constructs necessary to implement
-- the Michelson execution model

-- helper function to easily execute the CONTRACT instruction
appcontract : (P : Passable t) → CEnvironment → ⟦ addr ⟧
         → ⟦ option (contract P) ⟧
appcontract {t} P en adr
  with Environment.accounts en adr
... | nothing = nothing
... | just (p , s , c)
  with p ≟ t
... | no  _ = nothing
... | yes _ = just adr

-- like app-fct for Environment Functions, so we also need the environment
-- to implement these
app-enf : env-func args result → CEnvironment → Int args → ⟦ result ⟧
app-enf AMOUNT  en Iargs = Environment.amount  en
app-enf BALANCE en Iargs = Environment.balance en
app-enf (CONTRACT P) en (adr ∷ []) = appcontract P en adr

-- execution model for Program states
-- output stacks are arbitrary but fixed during execution
-- i don't want to mess up the code by including an explanation of every possible
-- execution step and it should'n be necessary. I explain some of them in the thesis
-- (sections 3.1 and 3.2) and the rest should be self explanatory with sufficient
-- knowledge of Michelson (see https://tezos.gitlab.io/michelson-reference)
--! progStep
prog-step : CProgState ro so → CProgState ro so

prog-step ρ
  with prg ρ
... | end = ρ
... | fct ft ; p
  = record ρ {  prg = p  ;
                rSI = (app-fct ft    (H.top (rSI ρ)) H.++ H.bot (rSI ρ)) }
... | enf ef ; p
  = record ρ {  prg = p  ;
                rSI = (app-enf ef (en ρ) (H.top (rSI ρ))   ∷ H.bot (rSI ρ)) }
... | DROP ; p
  = record ρ {  prg = p  ;
                rSI = H.bot (rSI ρ) }
... | DIP n dp ; p
  = record ρ {  prg =   dp ;∙ DIP' (take n (ri ρ)) ∙ p  ;
                rSI = H.drop n (rSI ρ) ;
                sSI = H.take n (rSI ρ) H.++ (sSI ρ) }
... | ITER ip ; p
  = record ρ {  prg = ITER'    ip ∙ p  ;
                rSI = H.drop 1 (rSI ρ) ;
                sSI = head (rSI ρ) ∷ sSI ρ }
... | IF-NONE thn els ; p
  with rSI ρ
... | just x ∷ rsi
  = record ρ {  prg = els ;∙ p  ;
                rSI =  x ∷ rsi }
... | nothing ∷ rsi
  = record ρ {  prg = thn ;∙ p  ;
                rSI =      rsi }
prog-step ρ | ITER' ip ∙ p
  with sSI ρ
... | [] ∷ ssi
  = record ρ {  prg = p ;
                sSI = ssi }
... | (x ∷ xs) ∷ ssi
  = record ρ {  prg =   ip ;∙ ITER'    ip ∙ p  ;
                rSI =  x ∷ rSI ρ ;
                sSI = xs   ∷ ssi }
prog-step ρ | DIP' top ∙ p
  = record ρ {  prg = p  ;
                rSI = H.top (sSI ρ) H.++ rSI ρ ;
                sSI = H.bot (sSI ρ) }


-- execution model of execution states, that is of executions of pending blockchain
-- operations or contract executions
-- when MPstate is just prg-running and the shadow program in its ProgState matches
-- end, the current contract execution has terminated.
-- because of the typing parameterization the shadow stack must be empty and the
-- real stack must contain the expected single pair of emitted operations new-ops
-- and updated storage value new-storage of the current contract
-- so new-ops can be appended to pending and the relevant contracts can be updated
-- we only allow a transfer-tokens operation to start an actual execution
-- (see below for an explanation on how these are handled)
-- if it comes with enough tokens to support that operations.
-- so at this stage we don't need to check if there were enough.
-- it must be NOTICED!!!! howevere that this will only be enforced automatically
-- when the user initializes an ExecState with MPstate = nothing and puts the
-- transfer operation to be executed in the pending list. BUT a CARELESS USER
-- could easily program a nonsensical ExecState where these constraints fail.
-- when the current contract execution hasn't terminated yet, the next ExecState
-- will be simply that where the ProgState is executed with prog-step
-- the remaining cases check pending operations, which currently can only contain
-- transfer-tokens operations to start a new contract execution
-- here a lot of parameters have to be checked (described in the thesis but also a bit
-- self explanatory; sadr is the account address that sent the transfer, cadr is the
-- target address)
-- with Contract.balance sender <? tok ensures that only transferes are executed
-- who's amount the sender can actually support, as mentioned above

-- when starting a `transfer-token value amount target` on behalf of a sender, we check if the sender 
-- has enough tokens to pay for `amount`. The transfer fails if not, otherwise we immediately
-- deduct the `amount` from the sender's balance.

--!! ExecStep
exec-step : CExecState → CExecState

--! ExecStepProgram
exec-step σ@(exc accts (inj₁ (pr self _ (state en end [ new-ops , new-storage ] [] _))) pend)
  = record σ{ accounts = set (Environment.self en) (updsrg self new-storage) accts
            ; MPstate  = inj₂ tt
            ; pending  = pend ++ [ new-ops , Environment.self en ] }
exec-step σ@(exc _ (inj₁ ρr@(pr _ _ ρ)) _)
  = record σ{ MPstate = inj₁ (record ρr{ ρ = prog-step ρ }) }

exec-step σ@(exc accounts (inj₂ tt) []) = σ
exec-step σ@(exc accounts (inj₂ tt) [ [] , send-addr // pending ])
  = record σ{ pending = pending }
exec-step σ@(exc accounts (inj₂ tt) [ [ transfer-tokens {ty} x tok self-addr // more-ops ]
                                  , send-addr // pending ])
  with accounts send-addr
... | nothing = record σ{ pending = pending }
... | just (p , _ , sender)
  with send-addr ≟ₙ self-addr
... | yes _
  with ty ≟ p
... | no  _    = record σ{ pending = [ more-ops , send-addr // pending ] }
... | yes refl
  = exc accounts
        (inj₁ (pr sender sender (state
          (env accounts self-addr send-addr (Contract.balance sender) zero) -- should be tok?
          (Contract.program sender ;∙ end)
          ((x , Contract.storage sender) ∷ []) [] _)))
        [ more-ops , send-addr // pending ]
exec-step σ@(exc accounts (inj₂ tt) [ [ transfer-tokens {ty} x tok self-addr // more-ops ]
                                  , send-addr // pending ])
    | just (_ , _ , sender) | no _
  with Contract.balance sender <? tok | accounts self-addr
... | yes _ | _       = record σ{ pending = [ more-ops , send-addr // pending ] }
... | no  _ | nothing = record σ{ pending = [ more-ops , send-addr // pending ] }
... | no  _ | just (p , _ , self)
  with ty ≟ p
... | no  _    = record σ{ pending = [ more-ops , send-addr // pending ] }
... | yes refl
  = exc accounts
        (inj₁ (pr self sender (state
          (env accounts self-addr send-addr (tok + Contract.balance self) tok)
          (Contract.program self ;∙ end)
          ((x , Contract.storage self) ∷ []) [] _)))
        [ more-ops , send-addr // pending ]

-- this is just a convenience function to execute several steps at once,
-- it does not faithfully reflect the gas consumption model of Michelson!!!
exec-exec : ℕ → CExecState → ℕ × CExecState
exec-exec zero starved = zero , starved
exec-exec (suc gas) σ@(exc _ (inj₁ _) _) = exec-exec gas (exec-step σ)
exec-exec (suc gas) σ@(exc _ (inj₂ _) (_ ∷ _)) = exec-exec gas (exec-step σ)
exec-exec (suc gas) σ@(exc _ (inj₂ _) []) = suc gas , σ

