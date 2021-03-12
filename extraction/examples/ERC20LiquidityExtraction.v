(** * Extraction of a simple counter contract *)

From Coq Require Import PeanoNat ZArith Notations.

From MetaCoq.Template Require Import Loader.
From MetaCoq.Erasure Require Import Loader.

From ConCert.Embedding Require Import MyEnv CustomTactics.
From ConCert.Embedding Require Import Notations.
(* From ConCert.Embedding Require Import SimpleBlockchain. *)
From ConCert.Embedding.Extraction Require Import PreludeExt.
From ConCert.Extraction Require Import LPretty LiquidityExtract Common Optimize.
From ConCert.Execution Require Import Automation.
From ConCert.Execution Require Import Serializable.
From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import EIP20Token.
From Coq Require Import List Ascii String.
Local Open Scope string_scope.

From MetaCoq.Template Require Import All.

Import ListNotations.
Import MonadNotation.

Open Scope Z.

Definition PREFIX := "".

Definition TT_remap_default : list (kername * string) :=
  [
    (* types *)
    remap <%% Z %%> "tez"
  ; remap <%% N %%> "nat"
  ; remap <%% nat %%> "nat"
  ; remap <%% bool %%> "bool"
  ; remap <%% unit %%> "unit"
  ; remap <%% list %%> "list"
  ; remap <%% @fst %%> "fst"
  ; remap <%% @snd %%> "snd"
  ; remap <%% option %%> "option"
  ; remap <%% gmap.gmap %%> "map"
  ; remap <%% positive %%> "nat"
  ; remap <%% Amount %%> "tez"
  ; remap <%% @Address %%> "address"

  (* operations *)
  ; remap <%% List.fold_left %%> "List.fold"
  ; remap <%% Pos.add %%> "addNat"
  ; remap <%% Pos.sub %%> "subNat"
  ; remap <%% Pos.leb %%> "leNat"
  ; remap <%% Pos.eqb %%> "eqNat"
  ; remap <%% Z.add %%> "addTez"
  ; remap <%% Z.sub %%> "subTez"
  ; remap <%% Z.leb %%> "leTez"
  ; remap <%% Z.ltb %%> "ltTez"
  ; remap <%% Z.eqb %%> "eqTez"
  ; remap <%% Z.gtb %%> "gtbTez"
  ; remap <%% N.add %%> "addInt"
  ; remap <%% N.sub %%> "subInt"
  ; remap <%% N.leb %%> "leInt"
  ; remap <%% N.ltb %%> "ltInt"
  ; remap <%% N.eqb %%> "eqInt"
  ; remap <%% andb %%> "andb"
  ; remap <%% negb %%> "not"
  ; remap <%% orb %%> "orb"

  (* Maps *)
  ; remap <%% @stdpp.base.insert %%> "Map.add"
  ; remap <%% @stdpp.base.lookup %%> "Map.find"
  ; remap <%% @stdpp.base.empty %%> "Map.empty"
  ; remap <%% @address_eqdec %%> ""
  ; remap <%% @address_countable %%> ""
  ].

From ConCert.Execution.Examples Require EIP20Token.

Section EIP20TokenExtraction.
  Import EIP20Token.
  From ConCert.Utils Require Import RecordUpdate.
  Import RecordSetNotations.
  Require Import Containers.
  From stdpp Require gmap.


  (* Notation storage := ((time_coq × Z × address_coq) × Maps.addr_map_coq × bool). *)
  Notation params := (ContractCallContext × option EIP20Token.Msg).
  Open Scope N_scope.

    (* A specialized version of FMap's partial alter, w.r.t. FMap Address N *)
  Definition partial_alter_addr_nat : string :=
       "let partial_alter_addr_nat (f : nat option -> nat option)" ++ nl
    ++ "                           (k : address)" ++ nl
    ++ "                           (m : (address,nat) map) : (address,nat) map =" ++ nl
    ++ "  match Map.find k m with" ++ nl
    ++ "    Some v -> Map.update k (f v) m" ++ nl
    ++ "  | None -> Map.update k (f (None : nat option)) m" ++ nl.

  Definition with_default_N : string :=
       "let with_default_N (n : nat) (m : nat option) : n =" ++ nl
    ++ "  match m with" ++ nl
    ++ "    Some m -> m" ++ nl
    ++ "  | None -> n".

  Definition ctx_from_ :=
    "let ctx_from (c : address * (address * tez )) = c.(0)".

  Definition test_try_transfer (from : Address)
      (to : Address)
      (amount : TokenValue)
      (state : State) : option State :=
    let from_balance := Extras.with_default 0 (FMap.find from state.(balances)) in
    if from_balance <? amount
    then None
    else let new_balances := FMap.add from (from_balance - amount) state.(balances) in
        let new_balances := FMap.partial_alter (fun balance => Some (Extras.with_default 0 balance + amount)) to new_balances in
        Some ({|
          balances := new_balances;
          total_supply := state.(total_supply);
          allowances := state.(allowances);
        |}).
  Open Scope bool_scope.
  Definition test_try_transfer_from (delegate : Address)
      (from : Address)
      (to : Address)
      (amount : TokenValue)
      (state : State) : option State :=
  match FMap.find from state.(allowances) with
  | Some from_allowances_map =>
  match FMap.find delegate from_allowances_map with
  | Some delegate_allowance =>
  let from_balance := Extras.with_default 0 (FMap.find from state.(balances)) in
  if (delegate_allowance <? amount) || (from_balance <? amount)
  then None
  else let new_allowances := FMap.add delegate (delegate_allowance - amount) from_allowances_map in
      let new_balances := FMap.add from (from_balance - amount) state.(balances) in
      let new_balances := FMap.partial_alter (fun balance => Some (Extras.with_default 0 balance + amount)) to new_balances in
      Some ({|
        balances := new_balances;
        allowances := FMap.add from new_allowances state.(allowances);
        total_supply := state.(total_supply)|})
  | _ => None
  end
  | _ => None
  end.

  Definition test_init (ctx : ContractCallContext) (setup : EIP20Token.Setup) : option EIP20Token.State :=
    Some {| total_supply := setup.(init_amount);
            balances := FMap.empty;
            allowances := FMap.empty |}.

  Open Scope Z_scope.
  Definition test_receive
      (ctx : ContractCallContext)
      (state : EIP20Token.State)
      (maybe_msg : option EIP20Token.Msg)
    : option (list ActionBody * EIP20Token.State) :=
    let sender := ctx.(ctx_from) in
    let without_actions := option_map (fun new_state => ([], new_state)) in
    match maybe_msg with
    | Some (transfer to amount) => without_actions (test_try_transfer sender to amount state)
    | Some (transfer_from from to amount) => without_actions (test_try_transfer_from sender from to amount state)
    (* Other endpoints are not included in this extraction test *)
    | _ => None
    end.

  Definition receive_wrapper
             (params : params)
             (st : State) : option (list ActionBody × State) :=
    test_receive params.1 st params.2.

  Definition init (ctx : ContractCallContext) (setup : EIP20Token.Setup) : option EIP20Token.State :=
    Some {| total_supply := setup.(init_amount);
            balances := FMap.add (EIP20Token.owner setup) (init_amount setup) FMap.empty;
            allowances := FMap.empty |}.
  Open Scope Z_scope.

  Definition EIP20Token_MODULE : LiquidityMod params ContractCallContext EIP20Token.Setup EIP20Token.State ActionBody :=
  {| (* a name for the definition with the extracted code *)
      lmd_module_name := "liquidity_eip20token" ;

      (* definitions of operations on pairs and ints *)
      lmd_prelude := prod_ops ++ nl ++ int_ops ++ nl 
                  ++ partial_alter_addr_nat ++ nl 
                  ++ with_default_N ++ nl
                  ++ ctx_from_ ;

      (* initial storage *)
      lmd_init := init ;

      lmd_init_prelude := "";

      (* the main functionality *)
      lmd_receive := receive_wrapper ;

      (* code for the entry point *)
      lmd_entry_point := printWrapper (PREFIX ++ "eip20token") ++ nl
      ++ printMain |}.

  Definition TT_remap_eip20token : list (kername * string) :=
  TT_remap_default ++ [
    (* remap <%% @ContractCallContext %%> "(adress * (address * int))" *)
    remap <%% eqb_addr %%> "eq_addr"
  ; remap <%% @Extras.with_default %%> "with_default_N"
  ; remap <%% @Monads.bind %%> "bind_option_state"
  ; remap <%% Monads.Monad_option %%> "()"

  ; remap <%% @stdpp.base.insert %%> "Map.add"
  ; remap <%% @stdpp.base.lookup %%> "Map.find"
  ; remap <%% @stdpp.base.empty %%> "Map.empty"
  ; remap <%% @stdpp.base.partial_alter %%> "partial_alter_addr_nat"
  ; remap <%% @gmap.gmap_partial_alter %%> ""
  ; remap <%% @fin_maps.map_insert %%> ""
  ; remap <%% @gmap.gmap_empty %%> ""
  ; remap <%% @gmap.gmap_lookup %%> ""
  ; remap <%% address_coq %%> "address"
  ; remap <%% @address_eqdec %%> ""
  ; remap <%% @address_countable %%> ""
  ; remap <%% option_map %%> "option_map_state_acts"
  ].

  Definition TT_rename_eip20token :=
    [ ("Z0" ,"0tez")
    ; ("N0", "0n")
    ; ("N1", "1n")
    ; ("nil", "[]")
    ; ("tt", "()") ].


  (* Compute (liquidity_extraction_test PREFIX TT_remap_eip20token TT_rename_eip20token EIP20Token_MODULE). *)

  Time MetaCoq Run
      (t <- liquidity_extraction_specialize PREFIX TT_remap_eip20token TT_rename_eip20token EIP20Token_MODULE ;;
      tmDefinition EIP20Token_MODULE.(lmd_module_name) t).

  Print liquidity_eip20token.

  (** We redirect the extraction result for later processing and compiling with the Liquidity compiler *)
  Redirect "./examples/liquidity-extract/liquidity_eip20token.liq" Compute liquidity_eip20token.


End EIP20TokenExtraction.




