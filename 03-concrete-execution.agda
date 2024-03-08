
module 03-concrete-execution where

open import 01-Types
open import 02-Functions-Interpretations

open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary

open import Data.Nat renaming (_≟_ to _≟ₙ_)
open import Data.List.Base hiding ([_])
open import Data.List.Relation.Unary.All using (All; _∷_; [])
open import Data.Maybe.Base hiding (map)
open import Data.Product hiding (map)

------------------------- Execution states and program execution ------------------------

-- contracts are parameterized by their parameter and storage types,
-- they provide evidence that these types are appropriate,
-- as well as their BALANCE and STORAGE (values) and a well typed program (NO shadow prog)
record Contract {p s : Type} : Set where
  constructor ctr
  field
    Pass : Passable p
    Stor : Storable s
    balance : ⟦ mutez ⟧
    storage : ⟦ s ⟧
    program : Program [ pair p s ] [ pair (list ops) s ]

-- for updating contracts when their execution terminated successfully
update : ∀ {p s} → Contract {p} {s} → ⟦ mutez ⟧ → ⟦ s ⟧ → Contract {p} {s}
update c blc srg = record c{ balance = blc ; storage = srg }
updsrg : ∀ {p s} → Contract {p} {s} →                  ⟦ s ⟧ → Contract {p} {s}
updsrg c     srg = record c{                 storage = srg }
subamn : ∀ {p s} → Contract {p} {s} → ⟦ mutez ⟧         → Contract {p} {s}
subamn c amn     = record c{ balance = Contract.balance c ∸ amn }

-- the blockchain maps any address to a contract if it stores one at that address
Blockchain : Set
Blockchain = ⟦ addr ⟧ → Maybe (∃[ p ] ∃[ s ] Contract {p} {s})

-- to set an address to a contract on a Blockchain
set : ∀ {p s} → ⟦ addr ⟧ → Contract {p} {s} → Blockchain → Blockchain
set adr c bl a
  with a ≟ₙ adr
... | yes refl = just (_ , _ , c)
... | no  ¬adr = bl a

-- empty Blockchain
∅ : Blockchain
∅ adr = nothing

-- this is the environment record that holds the informations necessary to execute
-- env-func instructions
-- it can easily be extended to enable more such instructions
-- the fields current and sender are currently not used for instructions but for
-- handling multi-contract executions where execution results are written back to
-- the blockchain and emitted operations can be executed in the same run
record Environment : Set where
  constructor env
  field
    accounts : Blockchain
    current  : ⟦ addr ⟧
    sender   : ⟦ addr ⟧
    balance  : ⟦ mutez ⟧
    amount   : ⟦ mutez ⟧

-- this is the program state used to execute any possible Michelson Program on
-- well typed stacks
-- parameterization with the expected output Stacks ensures that the execution
-- model and also the results from contract executions are well typed
-- (meaning they preserve the expected output Stacks)
-- the current stacks are Int's, i.e. typed stacks of values
-- some instructions are expanded to programs that include shadow instructions
record Prog-state {ro so : Stack} : Set where
  constructor state
  field
    {ri si} : Stack
    en  : Environment
    prg : ShadowProg ri si  ro so
    rSI : Int ri
    sSI : Int si

-- when not executing a single program but entire contracts and blockchain operations
-- this record encapsulates a Prog-state that is parameterized with the typing
-- restrictions for the 'current' contract that is executed
-- the sender is the account that triggered the current contract execution
-- it may be the same as current, and their addersses are saved in the Environment
-- of the Prog-state
-- they are saved in Prg-running because it was easier to implement
-- the update of a successfully terminated contract execution
-- by updating these contracts and saving them back to the blockchain (i.e. setting
-- their addresses on the blockchain to the updated contracts)
-- it could be possible that instead of saving the contract one could save something
-- like Exec-state.accounts current-address ≡ just (p , s , Contract {p} {s})
-- but it is probably a lot harder and i couldn't see any benefit in doing so
record Prg-running : Set where
  constructor pr
  field
    {p s x y} : Type
    current : Contract {p} {s}
    sender  : Contract {x} {y}
    ρ       : Prog-state {[ pair (list ops) s ]} {[]}
  
-- this is the execution state used to execute entire contracts and blockchain operations
-- when it's in a state where a contract is under execution, MPstate will have a value
-- just prg-running containing an approrpiate and well typed Prog-state
-- otherwise MPstate having the value nothing signals the execution model to handle
-- the next pending operation
-- those are saved as lists of pairs of lists since every contract emits a
-- (possibly empty) list of operations, the address of the emitter will be saved with it.
record Exec-state : Set where
  constructor exc
  field
    accounts : Blockchain
    MPstate  : Maybe Prg-running
    pending  : List (List Operation × ⟦ addr ⟧)


-- these are all the preliminary constructs necessary to implement
-- the Michelson execution model

-- helper function to easily execute the CONTRACT instruction
appcontract : (P : Passable t) → Environment → ⟦ addr ⟧
         → ⟦ option (contract P) ⟧
appcontract {t} P en adr
  with Environment.accounts en adr
... | nothing = nothing
... | just (p , s , c)
  with p ≟ t
... | no  _ = nothing
... | yes _ = just adr

-- like appft for Environment Functions, so we also need the environment
-- to implement these
appEF : ∀ {args result} → env-func args result → Environment → Int args → ⟦ result ⟧
appEF AMOUNT  en Iargs = Environment.amount  en
appEF BALANCE en Iargs = Environment.balance en
appEF (CONTRACT {ty} P) en (adr ∷ [I]) = appcontract P en adr

-- execution model for Program states
-- output stacks are arbitrary but fixed during execution
-- i don't want to mess up the code by including an explanation of every possible
-- execution step and it should'n be necessary. I explain some of them in the thesis
-- (sections 3.1 and 3.2) and the rest should be self explanatory with sufficient
-- knowledge of Michelson (see https://tezos.gitlab.io/michelson-reference)
prog-step : ∀ {ro so} → Prog-state {ro} {so} → Prog-state {ro} {so}
prog-step terminal@(state _ end _ _) = terminal
prog-step  ρ@(state _  (fct ft ; prg)   rSI _)
  = record ρ {  prg =            prg  ; rSI = (appft ft    (Itop rSI) +I+ Ibot rSI) }
prog-step  ρ@(state en (enf ef ; prg)   rSI sSI)
  = record ρ {  prg =            prg  ; rSI = (appEF ef en (Itop rSI)   ∷ Ibot rSI) }
prog-step  ρ@(state _    (IF-NONE thn els ; prg)   (nothing ∷ rSI) _)
  = record ρ {  prg =                thn ;∙ prg  ; rSI =      rSI }
prog-step  ρ@(state _    (IF-NONE thn els ; prg)   (just  x ∷ rSI) _)
  = record ρ {  prg =                els ;∙ prg  ; rSI =  x ∷ rSI }
prog-step  ρ@(state _        (ITER     ip ; prg)         (x ∷ rSI)               sSI)
  = record ρ {  prg =         ITER'    ip ∙ prg  ; rSI =      rSI ; sSI =    x ∷ sSI }
prog-step  ρ@(state _        (ITER'    ip ∙ prg)   _                       ([] ∷ sSI))
  = record ρ {  prg =                       prg  ;                  sSI =        sSI }
prog-step  ρ@(state _        (ITER'    ip ∙ prg)              rSI ([ x // xs ] ∷ sSI))
  = record ρ {  prg =   ip ;∙ ITER'    ip ∙ prg  ; rSI =  x ∷ rSI ; sSI = xs   ∷ sSI }
prog-step  ρ@(state {ri} _        (DIP  n   dp ; prg)   rSI sSI)
  = record ρ {  prg =   dp ;∙ DIP' (take n ri) ∙ prg  ; rSI = dropI n rSI
                                                 ; sSI = takeI n rSI +I+ sSI }
prog-step  ρ@(state _        (DIP' top    ∙ prg)   rSI sSI)
  = record ρ {  prg =                       prg  ; rSI = Itop sSI +I+ rSI
                                                 ; sSI = Ibot sSI }
prog-step  ρ@(state _        (DROP        ; prg)    (_ ∷ rSI) _)
  = record ρ {  prg =                       prg  ; rSI = rSI }

-- execution model of execution states, that is of executions of pending blockchain
-- operations or contract executions
-- when MPstate is just prg-running and the shadow program in its Prog-state matches
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
-- when the user initializes an Exec-state with MPstate = nothing and puts the
-- transfer operation to be executed in the pending list. BUT a CARELESS USER
-- could easily program a nonsensical Exec-state where these constraints fail.
-- when the current contract execution hasn't terminated yet, the next Exec-state
-- will be simply that where the Prog-state is executed with prog-step
-- the remaining cases check pending operations, which currently can only contain
-- transfer-tokens operations to start a new contract execution
-- here a lot of parameters have to be checked (described in the thesis but also a bit
-- self explanatory; sadr is the account address that sent the transfer, cadr is the
-- target address)
-- with Contract.balance sender <? tok ensures that only transferes are executed
-- who's amount the sender can actually support, as mentioned above
exec-step : Exec-state → Exec-state
exec-step σ@(exc
  accounts
  (just (pr current sender (state
    (env _ cadr sadr balance amount) end ((new-ops , new-storage) ∷ [I]) [I])))
  pending)
  with cadr ≟ₙ sadr
... | yes _ = record σ{ accounts = set cadr (updsrg current new-storage) accounts
                      ; MPstate  = nothing
                      ; pending  = pending ++ [ new-ops , cadr ] }
... | no  _ = record σ{ accounts = set cadr (update current balance new-storage)
                                 ( set sadr (subamn sender  amount) accounts)
                      ; MPstate  = nothing
                      ; pending  = pending ++ [ new-ops , cadr ] }
exec-step σ@(exc _ (just ρr@(pr _ _ ρ)) _)
  = record σ{ MPstate = just (record ρr{ ρ = prog-step ρ }) }
exec-step σ@(exc accounts nothing []) = σ
exec-step σ@(exc accounts nothing [ [] , sadr // pending ])
  = record σ{ pending = pending }
exec-step σ@(exc accounts nothing [ [ transfer-tokens {ty} x tok cadr // more-ops ]
                                  , sadr // pending ])
  with accounts sadr
... | nothing = record σ{ pending = pending }
... | just (p , _ , sender)
  with sadr ≟ₙ cadr
... | yes _
  with ty ≟ p
... | no  _    = record σ{ pending = [ more-ops , sadr // pending ] }
... | yes refl
  = exc accounts
        (just (pr sender sender (state
          (env accounts cadr sadr (Contract.balance sender) zero)
          (Contract.program sender ;∙ end)
          ((x , Contract.storage sender) ∷ [I]) [I])))
        [ more-ops , sadr // pending ]
exec-step σ@(exc accounts nothing [ [ transfer-tokens {ty} x tok cadr // more-ops ]
                                  , sadr // pending ])
    | just (_ , _ , sender) | no _
  with Contract.balance sender <? tok | accounts cadr
... | yes _ | _       = record σ{ pending = [ more-ops , sadr // pending ] }
... | no  _ | nothing = record σ{ pending = [ more-ops , sadr // pending ] }
... | no  _ | just (p , _ , current)
  with ty ≟ p
... | no  _    = record σ{ pending = [ more-ops , sadr // pending ] }
... | yes refl
  = exc accounts
        (just (pr current sender (state
          (env accounts cadr sadr (tok + Contract.balance current) tok)
          (Contract.program current ;∙ end)
          ((x , Contract.storage current) ∷ [I]) [I])))
        [ more-ops , sadr // pending ]

-- this is just a convenience function to execute several steps at once,
-- it does not faithfully reflect the gas consumption model of Michelson!!!
exec-exec : ℕ → Exec-state → ℕ × Exec-state
exec-exec zero starved = zero , starved
exec-exec (suc gas) σ@(exc _ (just _) _) = exec-exec gas (exec-step σ)
exec-exec (suc gas) σ@(exc _ nothing (_ ∷ _)) = exec-exec gas (exec-step σ)
exec-exec (suc gas) σ@(exc _ nothing []) = suc gas , σ

