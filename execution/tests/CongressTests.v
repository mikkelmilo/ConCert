From ConCert Require Import Blockchain LocalBlockchain Congress.
From ConCert Require Import Serializable.
From ConCert Require Import LocalBlockchainTests.
From ConCert Require Import BoundedN ChainedList.
Require Import Extras.

From ConCert.Execution.QCTests Require Import 
  ChainGens TestUtils ChainPrinters CongressGens CongressPrinters SerializablePrinters TraceGens.

Require Import ZArith Strings.Ascii Strings.String.

From QuickChick Require Import QuickChick. Import QcNotation.
From ExtLib.Structures Require Import Functor Applicative.
From ExtLib.Structures Require Import Monads.
Import MonadNotation. Open Scope monad_scope.
From Coq Require Import List. Import ListNotations.
From Coq Require Import Strings.BinaryString.
From Coq Require Import Morphisms.
From Coq Require Import Program.Basics.
Require Import Containers.

Notation "f 'o' g" := (compose f g) (at level 50).

Definition LocalChainBase : ChainBase := ChainGens.LocalChainBase.

Definition chain_with_congress_deployed : LocalChain := lcb_lc chain6. (* chain6 is from LocalBlockchainTests.v *)
Definition congress_chain := chain_with_congress_deployed.
Definition congress_contract_base_addr := BoundedN.of_Z_const AddrSize 128%Z.



Compute (show (lc_account_balances congress_chain)).
Compute (show (map fst (FMap.elements (lc_contracts congress_chain)))).
Compute (show (lc_contract_owners congress_chain)).
Compute (show (congressContractsMembers congress_chain)).
Compute (show (congressContractsMembers_nonempty_nonowners congress_chain)).
Compute (show (lc_proposals congress_chain)).

Definition init_is_valid p := 
  let ctx := fst p in
  let chain := (fst o snd) p in
  let setup := (snd o snd) p in
  match @Congress.init LocalChainBase chain ctx setup with
  | Some _ => checker true
  | None => false ==> true (* so we can see discards in QC output... *)
  end.

(* QuickChick (forAll (
  ctx <- gLocalChainContext 2 ;;
  cctx <- @gContractCallContext LocalChainBase ctx ;;
  chain <- gLocalChainSized 2 ctx ;;
  setup <- @arbitrary Setup _ ;;
  returnGen (cctx, (chain, setup)))
  init_is_valid). *)
(* coqtop-stdout:+++ Passed 10000 tests (0 discards) *)

Definition num_cacts_in_state_deployment_P chain ctx setup :=
match init chain ctx setup with
  | Some state => checker ((Congress.num_cacts_in_state state = 0)?)
  | None => (false ==> true) (* so we can see discards in QC output... *)
  end.

(* QuickChick (
  forAll4
    (gLocalChainContext 2)
    (fun ctx => gLocalChainSized 2 ctx)
    (fun _ _ => @arbitrary Setup _)
    (fun ctx _ _ => @gContractCallContext LocalChainBase ctx)
    (fun ctx chain setup cctx => num_cacts_in_state_deployment_P chain cctx setup)
). *)
(* coqtop-stdout:+++ Passed 10000 tests (0 discards) *)

(* What this says is that the number of actions to be performed by the congress never increases 
   more than the actions that are added in proposals, ie. actions can't appear out of nowhere. *)
(* If we replace '<=' with '<' QC finds a counterexample - a proposal can contain an empty list of actions, so they are equal before/after add_proposal *)
Definition add_proposal_cacts_P cacts chain (state : Congress.State) :=
  num_cacts_in_state (add_proposal cacts chain state) <=?
  num_cacts_in_state state + length cacts.

Definition gChainActionsFromCongressActions ctx : G (list CongressAction) :=
  (listOf (@gCongressActionSized ctx 2)).

Sample (ctx <- arbitrary ;; gChainActionsFromCongressActions ctx).
(* Compute (show (sample (gLocalChainContext 2))). *)

QuickChick (
  forAll4
    (gLocalChainContext 2)
    (fun ctx => gLocalChainSized 2 ctx)
    (fun ctx chain => @gStateSized ctx (current_slot chain) 2)
    (fun ctx _ _ => gChainActionsFromCongressActions ctx)
    (fun ctx chain state cacts => add_proposal_cacts_P cacts chain state)
).
(* coqtop-stdout:+++ Passed 10000 tests (0 discards) *)
Close Scope string_scope.

Definition vote_on_proposal_cacts_preserved_P addr pid vote_val state :=
  isSomeCheck 
    (vote_on_proposal addr pid vote_val state) 
    (fun new_state => checker 
      (num_cacts_in_state new_state =? num_cacts_in_state state)).

Definition check_vote_on_proposal_cacts_preserved := 
  forAll5
  (gLocalChainContext 4)
  (fun ctx => ctx_gAccountAddr ctx)
  (fun ctx _ => @gStateSized ctx 0 2)
  (fun _ _ _ => arbitrary)
  (fun _ _ state _ => gProposalIdFromState state) 
  (fun _ addr state vote_val pid => vote_on_proposal_cacts_preserved_P addr pid vote_val state).

Definition do_retract_vote_cacts_preserved_P addr pid state :=
  isSomeCheck
    (do_retract_vote addr pid state)
    (* Case where the above is 'Some new_state'  *)
    (fun new_state => checker
      (num_cacts_in_state new_state =? num_cacts_in_state state)).

(* TODO: look into what causes discards *)
Definition check_do_retract_vote_cacts_preserved_P :=
  forAll4
  (gLocalChainContext 4)
  (fun ctx => ctx_gAccountAddr ctx)
  (fun ctx _ => @gStateSized ctx 0 2)
  (fun _ _ state => gProposalIdFromState state) 
  (fun _ addr state pid => do_retract_vote_cacts_preserved_P addr pid state).

(* QuickChick check_do_retract_vote_cacts_preserved_P. *)
(* coqtop-stdout:+++ Passed 10000 tests (5888 discards) *)

(* Note to self: Look at implementation of 'vote_on_proposal' to get an idea of which implicit 
   requirements must met on the generated data *)
(* QuickChick (check_vote_on_proposal_cacts_preserved). *)
(* coqtop-stdout:+++ Passed 10000 tests (0 discards) *)
Open Scope bool_scope.

Definition receive_state_well_behaved_P
      chain ctx state msg :=
  isSomeCheck 
    (receive chain ctx state msg)
    (fun p => 
    let new_state := fst p in
    let resp_acts := snd p in  
    let cond : bool := (isSome msg) && (num_cacts_in_state new_state + length resp_acts <=?
                                  (num_cacts_in_state state +
                                  match msg with
                                  | Some (create_proposal ls) => length ls
                                  | _ => 0
                                  end)) 
    in checker cond).

(* fix: receive does not return Some... in most cases *)
Definition check_receive_state_well_behaved :=
  forAll5
    (gLocalChainContext 4)
    (fun ctx => gLocalChainSized 2 ctx)
    (fun ctx chain => @gStateSized ctx (current_slot chain) 2)
    (fun ctx _ _ => n <- arbitrary ;; liftM Some (gMsgSized ctx n))
    (fun ctx _ state  maybe_msg => match maybe_msg with 
                                   | Some msg =>  @gValidContractCallContext ctx (owner state) msg 
                                   | None => gContractCallContext ctx
                                   end)
    (fun _ chain state msg cctx => receive_state_well_behaved_P chain cctx state msg).

(* QuickChick check_receive_state_well_behaved. *)
(* coqtop-stdout:+++ Passed 10000 tests (7327 discards) *)

(* A property about the way States are generated. *)
(* It says that a State generated at some time slot cannot contain proposals later than this time slot.½ *)
Definition state_proposals_proposed_in_valid_P (time_slot : nat) (state : Congress.State) := 
  let proposals := map snd (FMap.elements (proposals state)) in
    forallb (fun p => proposed_in p <=? time_slot) proposals.

Definition check_state_proposals_proposed_in_valid := 
  forAll3
  (gLocalChainContext 4)
  (fun _ => arbitrary) (* time slot *)
  (fun ctx time_slot => @gStateSized ctx time_slot 2)
  (fun _ time_slot state => state_proposals_proposed_in_valid_P time_slot state).

(* QuickChick check_state_proposals_proposed_in_valid. *)
(* coqtop-stdout:+++ Passed 10000 tests (0 discards) *)

(* There are many issues with the property below
   Firstly: its incredibly hard to generate semantically well-formed data
   Secondly: its hard to avoid really sparse data w.r.t the property to be tested, ie. the 'isSomeCheck' will
      fail most of the time. This effect is amplified when they are nested
   Thirdly, its hard to interpret...
   Conclusion: this is perhaps abive the limit of 'functional' properties that we can test. This is probably due to the
      fact that there are so many quantified variables, many conditions in the property which have to be met
      and the fact that we quantify over *traces*.
      When dealing with traces, we should perhaps adopt a most constructive approach, and verify temporal-like properties instead. *)
(* Definition check_congress_txs_well_behaved_P :=
  forAll5
  (gLocalChainContext 4)
  (fun ctx => gLocalChainSized 4 ctx)
  (fun ctx ch => 
    env <- arbitrary ;; (* no generator for environments yet *)
    actions <- listOf (gActionOfCongress ctx 2) ;;
    mkChainStateGen LocalChainBase env  actions
  )
  (fun ctx ch bstate => ctx_gContractAddr ctx)
  (fun ctx ch bstate caddr => @gStateSized ctx 0 2)
  (fun ctx ch bstate caddr cstate => 
    let env := chain_state_env bstate in 
    isSome
      (env_contracts env caddr)
      (* (fun contract => checker true
        (* isSomeCheck
          (contract_state env caddr)
          (fun cstate =>
            isSomeCheck
             (@incoming_calls _ Msg _ bstate _ clnil caddr)
             (fun inc_calls => checker (
                num_cacts_in_state cstate +
                length (@outgoing_txs _ bstate _ clnil caddr) +
                length (outgoing_acts bstate caddr) <=?
                num_acts_created_in_proposals inc_calls))) *)
      )). *)
  ). *)

(* QuickChick check_congress_txs_well_behaved_P. *)
(* coqtop-stdout:*** Gave up! Passed only 0 tests
Discarded: 20000 *)

(* ---------------------- Tests on traces ----------------------  *)

Open Scope string_scope.
Definition debug_congress {A : Type} 
                         `{Checkable A} 
                          (lc : LocalChain) 
                          (acts_opt : option (list Action)) 
                          : A -> Checker := 
  whenFail (
    "LocalChain: " ++ show lc ++ nl ++
    "members: " ++ show (congressContractsMembers lc) ++ nl ++
    "active proposals: " ++ show (lc_proposals lc) ++ nl ++
    "contract owners: " ++ show (lc_contract_owners lc)
  ).
Close Scope string_scope.

(* coqtop-stdout:+++ Passed 10000 tests (0 discards) *)

Definition add_block_actions_succeeds_P c_opt actions_opt :=
  isSomeCheck c_opt
  (fun c => 
    (debug_congress c actions_opt) 
      (match actions_opt with
      | Some actions => (0 <? length actions) && isSome (my_add_block c actions)
      | None => false
      end)
  ).

Instance shrinkAction : Shrink Action := {| shrink a := [a] |}.

(* QuickChick (forAllShrink 
  (optToVector 1 (gCongressActionNew chain_with_congress_deployed 3))
  shrink
  (fun actions => add_block_actions_succeeds_P (Some chain_with_congress_deployed) (Some actions))). *)

Definition check_add_two_blocks_succeeds := 
  (forAll3 
    (optToVector 1 (gCongressActionNew chain_with_congress_deployed 2))
    (fun actions => returnGen (my_add_block chain_with_congress_deployed actions))
    (fun _ c_opt => 
      bindGenOpt (returnGen c_opt) 
      (fun c =>
        acts <- (optToVector 1 (gCongressActionNew c 2)) ;; 
        returnGen (Some acts)))
    (fun _ c_opt actions_opt => add_block_actions_succeeds_P c_opt actions_opt)
  ).

QuickChick check_add_two_blocks_succeeds.
(* coqtop-stdout:+++ Passed 10000 tests (0 discards) *)

Definition glctracetree (height : nat) := glctracetree_fix lc_initial gCongressActionNew height.
Definition glctracetreeFromLC lc (height : nat) := glctracetree_fix lc gCongressActionNew height.

(* QuickChick (forAllShrink
  (gCongressActionNew congress_chain 1)
  shrink
  (fun act_opt => isSomeCheck act_opt
    (fun act => 
      (debug_congress congress_chain (Some [act]) 
      (isSome (mk_basic_step_action congress_chain [act]))))    
)). *)
(* Wow!:
  coqtop-stdout:+++ Passed 10000 tests (0 discards) *)

(* Sample (bindGenOpt (gCongressActionNew congress_chain 3) (fun act => if isSome (mk_basic_step_action congress_chain [act]) 
                                                              then returnGen ( Some ("success", act)) 
                                                              else returnGen (Some ("fail", act)))). *)

Definition gCongressChainTraceList lc length := gLocalChainTraceList_fix lc gCongressActionNew length.

(* Sample (liftM allPaths (glctracetreeFromLC congress_chain 3)). *)

Sample (gCongressChainTraceList congress_chain 1 2).

Definition reachableFrom_congress (lc : LocalChain) pf : Checker := 
  @reachableFrom AddrSize lc (fun lc length => gCongressChainTraceList lc length 1) pf.

Notation "lc '~~>' pf" :=
  (reachableFrom_congress lc pf)
  (at level 88, left associativity).

Definition congress_has_votes_on_some_proposal lc := 
  0 <? FMap.size (lc_contract_members_and_proposals_with_votes lc).

(* QuickChick (congress_chain ~~> congress_has_votes_on_some_proposal o next_lc_of_lcstep). *)

(* This assumes that in a previous block, there was an active proposal *)
Definition congress_finished_a_vote (lc_step : @LocalChainStep AddrSize) :=
  match lc_step with
  | step_add_block _ _ _ => false
  | step_action _ _ _ acts => 
    let act_is_finish_vote (act : Action) := match act.(act_body) with 
                                             | act_call _ _ msg => match deserialize Congress.Msg _ msg with 
                                                                   | Some (Congress.finish_proposal _) => true 
                                                                   | _ => false end  
                                             | _ => false end in
    existsb act_is_finish_vote acts
  end.

QuickChick (congress_chain ~~> congress_finished_a_vote).