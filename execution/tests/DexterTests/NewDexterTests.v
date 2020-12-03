From ConCert Require Import Blockchain DexterBuggy.
From ConCert Require Import Serializable.
From ConCert Require Import Extras.
From ConCert Require Import Containers.
From ConCert Require Import BoundedN.
From ConCert Require Import ResultMonad.
From ConCert Require Import Monads.
Require Import ZArith.

From QuickChick Require Import QuickChick. Import QcNotation.
From ConCert.Execution.QCTests Require Import
  TestUtils TraceGens ChainPrinters SerializablePrinters.
From ConCert.Utils Require Import RecordUpdate.
From Coq Require Import List.
From Coq Require Import Morphisms.

Import ListNotations.
Import RecordSetNotations.

(* Use breadth-first execution for these tests, in order to emulate Tezos' execution model *)
Instance ChainBuilderBF : ChainBuilderType := LocalBlockchain.LocalChainBuilderBreadthFirst AddrSize.
Existing Instance ChainBuilderBF | 0.
Remove Hints ChainBuilderDF : typeclasses_instances.
Open Scope string_scope.

Existing Instance showChainTraceI.
Instance showChainBuilderBF : Show ChainBuilderBF :=
{|
  show cb := "Chain{| " ++ nl
             ++ show cb.(LocalBlockchain.lcb_trace)
             ++ "|}" ++ nl
|}.
Close Scope string_scope.
(* Print HintDb typeclass_instances. *)

Definition token_pool_size := 100%N.

Definition token_setup : EIP20Token.Setup := {|
  EIP20Token.owner := creator;
  EIP20Token.init_amount := token_pool_size%N;
|}.

Definition deploy_token : @ActionBody LocalChainBase := create_deployment 0 EIP20Token.contract token_setup.
Definition token_caddr : Address := BoundedN.of_Z_const AddrSize 128%Z.

Definition dexter_setup : DexterBuggy.Setup := {|
  token_caddr_ := token_caddr;
  token_pool_  := (token_pool_size - 40);  
|}.

(* The Dexter contract gets 30 money initially *)
Definition deploy_dexter : @ActionBody LocalChainBase := create_deployment 30 DexterBuggy.contract dexter_setup.
Definition dexter_caddr : Address := BoundedN.of_Z_const AddrSize 129%Z.

Definition add_as_operator_act owner operator tokens :=
  build_act owner (act_call token_caddr 0%Z  (serialize _ _ (EIP20Token.approve operator tokens))). 

Definition exchange_tokens_to_money_act owner amount := 
  build_act owner (act_call dexter_caddr 0%Z (serialize _ _ (DexterBuggy.tokens_to_asset {|
    exchange_owner := owner;
    tokens_sold := amount;
  |}))).


(* Setup a chain with fa2 contract, and dexter contract deployed.
   Also adds some tokens to person_1 and dexter contract, and adds some operators on the fa2 contract *)
Definition chain0 : ChainBuilderBF :=
  unpack_result (TraceGens.add_block builder_initial []).

Definition chain1 : ChainBuilderBF :=
  unpack_result (TraceGens.add_block chain0
  [  build_act creator (act_transfer person_1 10)
    (* ; build_act creator (act_transfer person_2 10) *)
    ; build_act creator deploy_token
    ; build_act creator deploy_dexter
    (* let creator transfer tokens on behalf of dexter *)
    (* ; add_as_operator_act dexter_caddr creator 100000%N *)
    
    (* transfer 100 tokens to person_1 *)
    ; build_act creator (act_call token_caddr 0%Z (serialize _ _ (EIP20Token.transfer person_1 40%N)))
    (* transfer 100 tokens to person_2 from dexter's reserve *)
    (* ; build_act creator (act_call token_caddr 0%Z (serialize _ _ (EIP20Token.transfer person_2 10%N))) *)
    (* transfer remaining tokens (majority) to dexter contract *)
    ; build_act creator (act_call token_caddr 0%Z (serialize _ _ (EIP20Token.transfer dexter_caddr (token_pool_size - 40)%N)))
    (* let dexter transfer tokens on behalf of person_1 and person_2 *)
    ; add_as_operator_act person_1 dexter_caddr token_pool_size
    ; add_as_operator_act person_2 dexter_caddr token_pool_size
  ]).

Definition add_block_with_acts (c : ChainBuilderBF) acts :=
  (TraceGens.add_block c acts).

Definition dexter_state env := get_contract_state DexterBuggy.State env dexter_caddr.
Definition token_state env := get_contract_state EIP20Token.State env token_caddr.

Module TestInfo <: DexterBuggyTestsInfo.
  Definition token_caddr := token_caddr.
  Definition dexter_contract_addr := dexter_caddr.
  Definition gAccountAddress := elems [person_1].
  Definition gAccountAddrWithout (ws : list Address) :=
    let addrs := filter (fun a => negb (existsb (address_eqb a) ws)) [person_1] in   
    elems_opt addrs.
End TestInfo.
Module MG := DexterBuggy.DexterBuggyGensMod TestInfo. Import MG.

(* Sample (gDexterAction chain1). *)

(* Sample (
 (liftM (fun a => add_block_with_acts chain1 [a]) (gDexterAction chain1)) 
). *)
(* Sample (gDexterChain 2 chain1 1). *)

Definition person_1_initial_balance : Amount := account_balance chain1 person_1.

Definition dexter_liquidity chain : Amount := account_balance chain dexter_caddr.

Definition account_tokens (env : Environment) (account : Address) : N :=
  with_default 0%N (
    do token_state <- token_state env ;
    FMap.find account token_state.(EIP20Token.balances)
    ).

Definition dexter_token_pool (env : Environment) : N :=
  with_default 0%N (
    do s <- dexter_state env ;
    Some s.(token_pool)
    ).

Compute (account_tokens chain1 dexter_caddr).
(* 80%N *)
Compute (account_tokens chain1 person_1).
(* 10%N *)
Compute (account_tokens chain1 person_2).
(* 10%N *)
Compute person_1_initial_balance.
(* 10%Z *)
Compute (dexter_liquidity chain1).
(* 30%Z *)

Open Scope Z_scope.
Coercion Z.of_N : N >-> Z.

(* given a list l of tokens to be exchanged, calculates the total price (in money)
   of the exchanges, if calculated correctly *)
Fixpoint price_of_exchanges l token_reserve asset_reserve := 
  match l with
  | tokens::l' =>
    let price := getInputPrice tokens token_reserve asset_reserve in
    price :: price_of_exchanges l' (tokens + token_reserve) (asset_reserve - price) 
  | [] => []
  end.

(* Asserts that exchanges are priced correctly, according to price_of_exchanges *)
Definition tokens_to_asset_correct_P_opt (old_env env : ChainState) : option Checker :=
  do state_dexterBuggy <- dexter_state env;
  (* only consider blocks that have been added after chain1 (the initialization chain) *)
  do _ <- if (env.(chain_height) <=? 2)%nat then None else Some tt ;
  let dexter_initial_balance := account_balance old_env dexter_caddr in
  let dexter_initial_token_reserve := account_tokens old_env dexter_caddr in
  let dexter_current_token_reserve := account_tokens env dexter_caddr in
  (* gather all exchange prices *)
  let exchanges : list Z := map (fun (act : Action) =>
    match act.(act_body) with
    | act_call _ _ serval =>
      match @deserialize DexterBuggy.Msg _ serval with
      | Some (tokens_to_asset p) => p.(tokens_sold)
      | _ => 0
      end
    | _ => 0
    end
  ) old_env.(chain_state_queue) in 
  let expected_prices := price_of_exchanges exchanges dexter_initial_token_reserve dexter_initial_balance in
  Some (
    whenFail (
      "history: " ++ show (state_dexterBuggy.(price_history)) ++ nl ++
      "queue: " ++ show old_env.(chain_state_queue) ++ nl ++
      "expected price history: " ++ show expected_prices
    )
    (checker (expected_prices = state_dexterBuggy.(price_history)?))
  ).

Definition tokens_to_asset_correct_P old_env env :=
  match tokens_to_asset_correct_P_opt old_env env with
  | Some p => p
  | None => checker true
  end.

Definition tokens_to_asset_correct chain_length :=
  forAllChainStatePairs chain_length chain1 (gDexterChain 2) tokens_to_asset_correct_P.

QuickChick (tokens_to_asset_correct).

Compute (account_balance chain1 person_1).
(* 10 *)
Compute (account_balance chain1 dexter_caddr).
(* 30 *)
Compute (getInputPrice 15 60 30).
(* 5 *)
(* The expected (correct) price of the second exchange of 16 tokens: *)
Compute (getInputPrice 16 75 25).
(* 4 *)
(* The incorrect calculation, where the token reserve has been updated, but not the asset reserve *)
(* This is what happens when an exchange is "injected" after another exchange, with the buggy implementation
   of dexter. *)
Compute (getInputPrice 16 75 30).
(* 5 *)