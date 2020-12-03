(* A token-asset exchange contract based on Dexter *)

From Coq Require Import ZArith.
From Coq Require Import Morphisms.
Require Monads.
Require Import Extras.
Require Import Containers.
Require Import Automation.
From ConCert.Utils Require Import RecordUpdate.
From Coq Require Import List.
Require Import Serializable.
Require Import Blockchain.
Import ListNotations.
Import RecordSetNotations.
From Coq Require Import Program.Basics.
Notation "f 'o' g" := (compose f g) (at level 50).
(* Require Import EIP20Token FA2Interface. *)
Require Import EIP20Token.

(* A liquidity exchange contract inspired by the Dexter contract.
   Allows for exchanging tokens to money, and allows the owner to add tokens to the
   reserve held by this contract. *)
Section DexterBuggy.
Import Monads.
Context {BaseTypes : ChainBase}.
Set Primitive Projections.
Set Nonrecursive Elimination Schemes.
Open Scope N_scope.

Record exchange_param :=
  build_exchange_param {
    exchange_owner : Address;
    tokens_sold : N;
  }.

Global Instance exchange_paramserializable : Serializable exchange_param :=
  Derive Serializable exchange_param_rect <build_exchange_param>.

Inductive Msg :=
  | tokens_to_asset : exchange_param -> Msg
  | add_to_tokens_reserve : Msg.

Global Instance DexterMsg_serializable : Serializable Msg :=
  Derive Serializable Msg_rect <tokens_to_asset, add_to_tokens_reserve>.

Record Setup :=
  build_setup {
    token_caddr_ : Address;
    token_pool_ : N;
  }.

Record State :=
  build_state {
    token_pool : N;
    price_history : list Amount;
    token_caddr : Address;
  }.

MetaCoq Run (make_setters State).
MetaCoq Run (make_setters Setup).

Section Serialization.

Global Instance setup_serializable : Serializable Setup :=
  Derive Serializable Setup_rect <build_setup>.

Global Instance state_serializable : Serializable State :=
  Derive Serializable State_rect <build_state>.

End Serialization.

Definition returnIf (cond : bool) := if cond then None else Some tt.
Definition require (cond : bool) := if cond then Some tt else None.
Definition address_not_eqb a b := negb (address_eqb a b).

(* calculates exchange rate *)
Open Scope Z_scope.
Definition getInputPrice (tokens_to_be_sold : Amount)
                         (tokens_reserve : Amount)
                         (asset_reserve : Amount)
                         :=
  Z.div (tokens_to_be_sold * 997 * asset_reserve) (tokens_reserve * 1000 + tokens_to_be_sold * 997).


Definition begin_exchange_tokens_to_assets (dexter_asset_reserve : Amount)
                                           (caller : Address)
                                           (params : exchange_param)
                                           (dexter_caddr : Address)
                                           (state : State)
                                           : option (State * (list ActionBody)) :=
  do _ <- require (address_eqb caller params.(exchange_owner)) ;
  let tokens_to_sell := Z.of_N params.(tokens_sold) in
  let tokens_price := getInputPrice tokens_to_sell (Z.of_N state.(token_pool)) dexter_asset_reserve in
  (* send out asset transfer to transfer owner, and send a token transfer message to the FA2 token *)
  let asset_transfer_msg := act_transfer params.(exchange_owner) tokens_price in
  let token_transfer_param := 
    EIP20Token.transfer_from params.(exchange_owner) dexter_caddr params.(tokens_sold)  in
  let token_transfer_msg := act_call state.(token_caddr) 0%Z (@serialize EIP20Token.Msg _ (token_transfer_param)) in
  let new_state := state<|token_pool := N.add state.(token_pool) params.(tokens_sold)|>
                        <| price_history := state.(price_history) ++ [tokens_price]|> in
  Some (new_state, [asset_transfer_msg; token_transfer_msg]).

Open Scope Z_scope.
Definition receive (chain : Chain)
                    (ctx : ContractCallContext)
                   (state : State)
                   (maybe_msg : option Msg)
                   : option (State * list ActionBody) :=
  let sender := ctx.(ctx_from) in
  let caddr := ctx.(ctx_contract_address) in
  let dexter_balance := chain.(account_balance) caddr in
  let amount := ctx.(ctx_amount) in
  match maybe_msg with
  | Some (tokens_to_asset params) => begin_exchange_tokens_to_assets dexter_balance sender params caddr state
  (* | Some add_to_tokens_reserve =>  *)
  (* Ignore any other type of call to this contract *)
  | _ => Some (state, [])
  end.

Definition init (chain : Chain)
                (ctx : ContractCallContext)
                (setup : Setup) : option State :=
  Some {| token_pool := setup.(token_pool_);
          token_caddr := setup.(token_caddr_);
          price_history := [] |}.

Lemma init_proper :
  Proper (ChainEquiv ==> eq ==> eq ==> eq) init.
Proof. repeat intro; solve_contract_proper.	Qed.

Lemma receive_proper :
  Proper (ChainEquiv ==> eq ==> eq ==> eq ==> eq) receive.
Proof. repeat intro; solve_contract_proper. Qed.

Definition contract : Contract Setup Msg State :=
  build_contract init init_proper receive receive_proper.

End DexterBuggy.


From ConCert Require Import Serializable.
From ConCert.Execution.QCTests Require Import TestUtils.
From QuickChick Require Import QuickChick.
Section DexterBuggyPrinters.

  Context `{Show Address}.
  Local Open Scope string_scope.

  Instance showDexterExchangeParam : Show DexterBuggy.exchange_param :=
  {|
    show t := "exchange{"
              ++ "exchange_owner: " ++ show t.(exchange_owner) ++ sep
              ++ "tokens_sold: " ++ show t.(tokens_sold)
              ++ "}"
  |}.

  Instance showDexterMsg : Show DexterBuggy.Msg :=
  {|
    show m := match m with
              | tokens_to_asset param => "token_to_asset " ++ show param
              | add_to_tokens_reserve => "add_to_tokens_reserve"
              end
  |}.


  Instance showDexterState : Show DexterBuggy.State :=
  {|
    show t := "DexterState{"
              ++ "token_caddr: " ++ show t.(token_caddr) ++ sep
              ++ "token_pool: " ++ show t.(token_pool) ++ sep
              ++ "price_history: " ++ show t.(price_history)
              ++ "}"
  |}.

  Instance showDexterSetup : Show DexterBuggy.Setup :=
  {|
    show t := "EIP20TokenSetup{"
              ++ "token_caddr_: " ++ show t.(token_caddr_) ++ sep
              ++ "token_pool_: " ++ show t.(token_pool_)
              ++ "}"
  |}.

End DexterBuggyPrinters.

(* From ConCert Require Import Containers.
From ConCert Require Import BoundedN.

From QuickChick Require Import QuickChick. Import QcNotation.
From ConCert.Execution.QCTests Require Import
  TestUtils TraceGens SerializablePrinters.
From Coq Require Import ZArith List. Import ListNotations. *)
From ConCert.Execution.QCTests Require Import TraceGens.
  (* For monad notations *)
From ExtLib.Structures Require Import Monads.
Import MonadNotation. Open Scope monad_scope.

  Module Type DexterBuggyTestsInfo.
    Parameter token_caddr : Address.
    Parameter dexter_contract_addr : Address.
    Parameter gAccountAddress : G Address.
    Parameter gAccountAddrWithout : list Address -> GOpt Address.
  End DexterBuggyTestsInfo.

  Module DexterBuggyGensMod (Info : DexterBuggyTestsInfo).
  Import Info.

  Arguments SerializedValue : clear implicits.
  Arguments deserialize : clear implicits.
  Arguments serialize : clear implicits.


  (* --------------------- FA2 Contract Generators --------------------- *)
  Section DexterBuggyGens.

  Definition gTokensToExchange (balance : N) : G (option N) :=
    if N.eqb 0%N balance
    then returnGen None
    else
      amount <- choose (1%N, balance) ;;
      returnGenSome amount.

  Definition gTokenExchange (state : EIP20Token.State) (caller : Address) : G (option DexterBuggy.Msg):=
    let caller_tokens : N := Extras.with_default 0%N (FMap.find caller state.(balances)) in
    tokens_to_exchange <- gTokensToExchange caller_tokens ;;
    let exchange_msg := {|
      exchange_owner := caller;
      tokens_sold := tokens_to_exchange;
    |} in
    returnGenSome (DexterBuggy.tokens_to_asset exchange_msg)
  .

  Definition liftOptGen {A : Type} (g : G A) : GOpt A :=
    a <- g ;;
    returnGenSome a.

  (* Definition gAddTokensToReserve (c : Chain)
                                (state : EIP20Token.State)
                                : GOpt (Address * Amount * DexterBuggy.Msg) :=
    tokenid <- liftM fst (sampleFMapOpt state.(assets)) ;;
    caller <- liftOptGen gAccountAddress ;;
    amount <- liftOptGen (choose (0%Z, c.(account_balance) caller)) ;;
    returnGenSome (caller, amount, (other_msg (add_to_tokens_reserve tokenid))). *)

  Definition gDexterAction (env : Environment) : GOpt Action :=
    let mk_call caller_addr amount msg :=
      returnGenSome {|
        act_from := caller_addr;
        act_body := act_call dexter_contract_addr amount (serialize DexterBuggy.Msg _ msg)
      |} in
    token_state <- returnGen (get_contract_state EIP20Token.State env token_caddr) ;;
    backtrack [
      (* (1, '(caller, amount, msg) <- gAddTokensToReserve env token_state ;;
          mk_call caller amount msg
      ) ; *)
      (2, caller <- gAccountAddrWithout [token_caddr; dexter_contract_addr] ;;
          msg <- gTokenExchange token_state caller ;;
          mk_call caller 0%Z msg
      )
    ].

  Context {ChainBuilder : ChainBuilderType}.
  Context `{Show ChainBuilder}.
  Definition gDexterChain max_acts_per_block cb length :=
    gChain cb (fun e _ => gDexterAction e) length 1 max_acts_per_block.

  (* the '1' fixes nr of actions per block to 1 *)
  Definition token_reachableFrom max_acts_per_block cb pf : Checker :=
    reachableFrom_chaintrace cb (gDexterChain max_acts_per_block) pf.

  Definition token_reachableFrom_implies_reachable 
            {A} length max_acts_per_block cb (pf1 : ChainState -> option A) pf2 : Checker :=
    reachableFrom_implies_chaintracePropSized length cb (gDexterChain max_acts_per_block) pf1 pf2.

  End DexterBuggyGens.
End DexterBuggyGensMod.

Module DummyTestInfo <: DexterBuggyTestsInfo.
  Definition token_caddr := zero_address.
  Definition dexter_contract_addr := zero_address.
  Definition exploit_contract_addr := zero_address.
  Definition gAccountAddress := returnGen zero_address.
  Definition gAccountAddrWithout (w : list Address) := returnGenSome zero_address.
End DummyTestInfo.
Module MG := DexterBuggyGensMod DummyTestInfo. Import MG.


  

