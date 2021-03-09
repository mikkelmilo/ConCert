(** * Extraction of a simple counter contract *)

From Coq Require Import PeanoNat ZArith Notations.

From MetaCoq.Template Require Import Loader.
From MetaCoq.Erasure Require Import Loader.

From ConCert.Embedding Require Import MyEnv CustomTactics.
From ConCert.Embedding Require Import Notations.
From ConCert.Embedding Require Import SimpleBlockchain.
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
Import AcornBlockchain.
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
  ; remap <%% @stdpp.base.lookup %%> "Map.find_opt"
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
  (* Definition crowdfunding_init (ctx : SimpleCallCtx)
             (setup : (time_coq × Z × address_coq)) : option storage :=
    if ctx.2.2.1 =? 0 then Some (setup, (Maps.mnil, false)) else None.
    (* (unfolded Init.init) setup ctx. *)
   *)
  Definition receive (ctx : ContractCallContext)
                     (state : State)
                     (maybe_msg : option Msg) : option (list ActionBody * State) :=
    let sender := ctx.(ctx_from) in
    let without_actions := option_map (fun new_state => ([], new_state)) in
    (* Only allow calls with no money attached *)
    if ctx.(ctx_amount) >? 0
    then None
    else match maybe_msg with
   | Some (transfer to amount) => without_actions (try_transfer sender to amount state)
   | Some (transfer_from from to amount) => without_actions (try_transfer_from sender from to amount state)
   | Some (approve delegate amount) => without_actions (try_approve sender delegate amount state)
   (* transfer actions to this contract are not allowed *)
         | None => None
   end.

  Definition receive_wrapper
             (params : params)
             (st : State) : option (list ActionBody × State) :=
    receive params.1 st params.2.

  Definition init (ctx : ContractCallContext) (setup : EIP20Token.Setup) : option EIP20Token.State :=
    Some {| total_supply := setup.(init_amount);
            balances := FMap.add (EIP20Token.owner setup) (init_amount setup) FMap.empty;
            allowances := FMap.empty |}.
  Open Scope Z_scope.

  (* A specialized version of FMap's partial alter, w.r.t. FMap Address N *)
  Definition partial_alter_addr_nat : string :=
       "let partial_alter_addr_nat (f : nat option -> nat option)" ++ nl
    ++ "                           (k : address)" ++ nl
    ++ "                           (m : (address,nat) map) : (address,nat) map =" ++ nl
    ++ "  match Map.find_opt k m with" ++ nl
    ++ "    Some v -> Map.update k (f v) m" ++ nl
    ++ "  | None -> Map.update k (f (None : nat option)) m" ++ nl.

  Definition option_map_state_acts : string :=
       "let option_map_state_acts (f : state -> (state * operation list)) (o : state option) =" ++ nl
    ++ "  match o with" ++ nl
    ++ "    Some a -> Some (f a)" ++ nl
    ++ "    | None -> (None : (state * operation list))".

  Definition bind_option_state : string :=
       "let bind_option_state (a, b, c : unit) (m : state option) (f : state -> state option) : state option =" ++ nl
    ++ "match m with" ++ nl
    ++ "    Some a -> f a" ++ nl
    ++ "  | None -> (None : state option)".

  Definition with_default_N : string :=
       "let with_default_N (n : nat) (m : nat option) : n =" ++ nl
    ++ "  match m with" ++ nl
    ++ "    Some m -> m" ++ nl
    ++ "  | None -> n".

    (* LiquidityMod msg _ (Z × address) storage operation *)
  Definition EIP20Token_MODULE : LiquidityMod params _ EIP20Token.Setup EIP20Token.State ActionBody :=
  {| (* a name for the definition with the extracted code *)
      lmd_module_name := "liquidity_eip20token" ;

      (* definitions of operations on pairs and ints *)
      lmd_prelude := prod_ops ++ nl ++ int_ops;

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
    remap <%% @ContractCallContext %%> "(adress * (address * int))"
  ; remap <%% eqb_addr %%> "eq_addr"
  ; remap <%% @Extras.with_default %%> "with_default_N"
  ; remap <%% @Monads.bind %%> "bind_option_state"
  ; remap <%% Monads.Monad_option %%> "()"

  ; remap <%% @stdpp.base.insert %%> "Map.add"
  ; remap <%% @stdpp.base.lookup %%> "Map.find_opt"
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
      (* monad hack *)
    ; ("Monad_option", "()")
    ; ("tt", "()") ].

  (* Time MetaCoq Run
  (t <- CameLIGO_extraction PREFIX TT_remap_eip20token TT_rename_eip20token LIGO_EIP20Token_MODULE ;;
    tmDefinition LIGO_EIP20Token_MODULE.(lmd_module_name) t
  ).

  Print cameLIGO_eip20token.

  Definition printed := Eval vm_compute in cameLIGO_eip20token.
    (** We redirect the extraction result for later processing and compiling with the CameLIGO compiler *)
  Redirect "examples/cameligo-extract/eip20tokenCertifiedExtraction.ligo" MetaCoq Run (tmMsg printed). *)

  (** We run the extraction procedure inside the [TemplateMonad].
      It uses the certified erasure from [MetaCoq] and the certified deboxing procedure
      that removes application of boxes to constants and constructors. *)

  Time MetaCoq Run
      (t <- liquidity_extraction PREFIX TT_remap_eip20token TT_rename_eip20token EIP20Token_MODULE ;;
      tmDefinition EIP20Token_MODULE.(lmd_module_name) t).

  Print liquidity_eip20token.

  (** We redirect the extraction result for later processing and compiling with the Liquidity compiler *)
  Redirect "./examples/liquidity-extract/liquidity_eip20token.liq" Compute liquidity_eip20token.


End EIP20TokenExtraction.




