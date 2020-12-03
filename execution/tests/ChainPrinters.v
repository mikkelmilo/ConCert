From ConCert Require Import Blockchain LocalBlockchain TestUtils.
From ConCert Require Import Serializable. Import SerializedType.
From ConCert Require Import BoundedN ChainedList ResultMonad.

From QuickChick Require Import QuickChick. Import QcNotation.

From Coq Require Import ZArith Strings.String.
From Coq Require Import List. Import ListNotations.
Import BoundedN.Stdpp.

Let Base := TestUtils.LocalChainBase.

Close Scope address_scope.
Open Scope list_scope.
Open Scope string_scope.

(* Derive Show for positive. *)
Derive Show for SerializedType.

Derive Show for result.
Derive Show for ActionEvaluationError.

Instance showContract {Setup Msg State : Type}
                     `{Serializable Setup}
                     `{Serializable Msg}
                     `{Serializable State}
                      : Show (Contract Setup Msg State) :=
{|
  show c := "Contract{...}"
|}.

Instance showEnvironment (BaseTypes : ChainBase) `{Show Chain}: Show Environment :=
{|
  show env := "Environment{"
              ++ "chain: " ++ show (env_chain env) ++ sep
              ++ "contract states:..."             ++ "}"
|}.

Fixpoint string_of_interp_type (st : SerializedType) :  (interp_type st) -> string :=
match st as st0 return interp_type st0 -> string with
  | ser_unit => fun _ => "()"
  | ser_int => fun t => show t
  | ser_bool => fun t => show t
  | ser_list a =>
    fun t : list (interp_type a) =>
      let t_str_list := map (string_of_interp_type a) t in
      "[" ++ String.concat ";" t_str_list ++ "]"
  | ser_pair a b =>
    fun t : (interp_type a * interp_type b) =>
      "("
      ++ string_of_interp_type a (fst t)
      ++ ","
      ++ string_of_interp_type b (snd t) ++ ")"
  end.

Definition ex_serialized_type := ser_pair (ser_list (ser_list ser_bool)) ser_int.
(* Compute (interp_type ex_serialized_type). *)
Definition ex_val := ([[true;false];[true;true];[false];[]], 2%Z).
(* Compute (string_of_interp_type ex_serialized_type ex_val). *)

(* Show and Generator instances for types related to Traces (an execution sequence of contracts on the BC) *)
Instance showBlockHeader (BaseTypes : ChainBase) `{Show (@Address BaseTypes)} : Show (@BlockHeader BaseTypes) :=
  {|
    show bh :=
      "BlockHeader{" ++ "bheight: "     ++ show (block_height bh)           ++ sep
                     ++ "bslot: "       ++ show (block_slot bh)             ++ sep
                     ++ "bfin_height: " ++ show (block_finalized_height bh) ++ sep
                     ++ "breward: "     ++ show (block_reward bh)           ++ sep
                     ++ "bcreator: "    ++ show (block_creator bh)          ++ "}"
  |}.

  (* We dont show the bound because it may be a very large number which, when converted to nat and then to string, gives a memory overflow. *)
Instance showBoundedN {bound : N} `{Show N} : Show (BoundedN.BoundedN bound) :=
{|
  show bn := match bn with | BoundedN.bounded n _ => show n ++ "%" ++ show bound end
|}.

Instance showBoundedNAddrSize : Show (BoundedN.BoundedN AddrSize) :=
{|
  show := @show (BoundedN.BoundedN AddrSize) showBoundedN
|}.

Instance showAddress : Show (@Address Base) :=
{|
  show := @show (BoundedN.BoundedN AddrSize) showBoundedNAddrSize
|}.

Instance showLocalChain : Show (@LocalChain AddrSize) :=
{|
  show lc := "LocalChain{"
              ++ show (lc_height lc) ++ sep
              ++ show (lc_slot lc)   ++ sep
              ++ show (lc_fin_height lc)
              ++ sep ++ "... }"
|}.

Instance showLocalContractCallContext : Show (@ContractCallContext Base) :=
{|
show cctx := "ContractCallContext{"
             ++ "ctx_from: " ++ show (@ctx_from Base cctx) ++ sep
             ++ "ctx_contract_addr: " ++ show (@ctx_contract_address Base cctx) ++ sep
             ++ "ctx_amount: " ++ show (@ctx_amount Base cctx) ++ "}"
|}.

Instance showActionBody `{Show SerializedValue} : Show ActionBody :=
{|
  show a := match a with
    | act_transfer addr amount =>
      "(act_transfer " ++ show addr ++ sep ++ show amount ++ ")"
    | act_call addr amount ser_value =>
      "(act_call " ++ show addr ++ sep ++ show amount ++ sep ++ show ser_value ++ ")"
    | act_deploy amount contract ser_value =>
      "(act_deploy " ++ show amount ++ sep ++ show ser_value ++ ")"
    end
|}.

Instance showLocalAction `{Show ActionBody} : Show (@Action Base) :=
{|
  show a := "Action{"
            ++ "act_from: " ++ show (act_from a) ++ sep
            ++ "act_body: " ++ show (act_body a) ++ "}"
|}.

Instance showLocalActionList `{Show (@Action Base)}: Show (list (@Action Base)) :=
{|
  show a := String.concat (";" ++ nl) (map show a)
|}.
Existing Instance showLocalActionList | 0.

Instance showOptLocalActionList `{Show (option (@Action Base))}: Show (list (option (@Action Base))) :=
{|
  show a := String.concat (";" ++ nl) (map show a)
|}.
Existing Instance showOptLocalActionList | 0.

Instance showChainState `{Show Environment} `{Show (@Action Base)} : Show (@ChainState Base) :=
{|
  show a := "ChainState{"
            ++ "env: " ++ show a.(chain_state_env) ++ sep
            ++ "queue: " ++ show a.(chain_state_queue) ++ "}"
|}.

Instance showContractCallInfo {Msg : Type} `{Show Msg} : Show (ContractCallInfo Msg) :=
{|
  show info := "ContractCallInfo{"
                ++ "call_from: " ++ show (call_from info) ++ sep
                ++ "call_amount: " ++ show (call_amount info) ++ sep
                ++ "call_msg: " ++ show (call_msg info) ++ sep ++ "}"
|}.

(* Show instanced related to ChainedLists and ChainTraces *)

Instance showAddBlockError `{Show (@Action Base)} : Show AddBlockError :=
{|
  show err := match err with
              | invalid_header => "invalid_header"
              | invalid_root_action act => "invalid_root_action: " ++ show act
              | action_evaluation_depth_exceeded => "action_evaluation_depth_exceeded"
              | action_evaluation_error act eval_error =>
                "action_evaluation_error for " ++ show act ++ " with error: " ++ show eval_error
              end
|}.

(* retrieves the previous and next state of a ChainStep *)
Definition chainstep_states {prev_bstate next_bstate} (step : ChainStep prev_bstate next_bstate) :=
  (prev_bstate, next_bstate).

Instance showChainTraceI `{Show (@Action Base)} {from to} : Show (ChainTrace from to) :=
{|
  show :=
    let fix showChainTrace {from to : ChainState} (trace : ChainTrace from to) :=
      match trace with
      | snoc trace' step =>
      match step with
      | Blockchain.step_block _ _ _ _ _ _ _ =>
          let '(_, next_bstate) := chainstep_states step in
          showChainTrace trace' ++ nl ++
          "Block " ++ show next_bstate.(current_slot) ++ " [" ++ nl ++
            show next_bstate.(chain_state_queue)
          ++ "];"
        | _ => showChainTrace trace'
        end
      | clnil  => ""
      end in
    showChainTrace
|}.

Instance showLCB `{Show (@Action Base)} : Show ChainBuilderDF :=
{|
  show cb := "Chain{| " ++ nl
             ++ show cb.(lcb_trace)
             ++ "|}" ++ nl
|}.

Instance showChainBuilderType {BaseTypes : ChainBase}: Show (@ChainBuilderType BaseTypes) :=
  {| show a := "ChainBuilderType{...}" |}.

Instance showChain (BaseTypes : ChainBase) : Show (@Chain BaseTypes) :=
{|
  show c :=
    let height := show (chain_height c) in
    let slot := show (current_slot c) in
    let fin_height := show (finalized_height c) in
      "Chain{" ++ "height: "       ++ height     ++ sep
                ++ "current slot: " ++ slot       ++ sep
                ++ "final height: " ++ fin_height ++ "}"
|}.

Close Scope string_scope.
Close Scope list_scope.
