(* 
  The ChainTrace datatype is defined as a ChainedList of ChainStates and ChainSteps.
  The ChainStep is an inductive relation with constructors 'step_block', 'step_action', and 'step_permute'.
  Each constructor is guarded with a number of propositions, requiring various validity conditions.
  
  This makes it hard to construct a generator for the ChainTrace type, so instead we initially construct a simpler model
  for chain traces, which is essentially just a list of chain states.
  But since we are working in the context of black-box testing, this may even be a better approach than trying to implement
  generators for the ChainTrace type, since we don't want to ensure/require that certain conditions hold, we only want
  to generate data from the given functions, and see what result we get. 
*)

Global Set Warnings "-extraction-logical-axiom".

Require Import ZArith Strings.Ascii Strings.String.
From QuickChick Require Import QuickChick. Import QcNotation.
From ExtLib.Structures Require Import Functor Applicative.

From ConCert Require Import Blockchain.
From ConCert Require Import LocalBlockchain.
From ConCert Require Import Serializable.
From ConCert Require Import BoundedN ChainedList.
From ConCert Require Import LocalBlockchainTests.
From ConCert Require Import Containers.
From ConCert Require Import EIP20Token.
Require Import Extras.

From ConCert.Execution.QCTests Require Import ChainGens TestUtils ChainPrinters CongressPrinters CongressGens SerializablePrinters EIP20TokenPrinters EIP20TokenGens.

(* For monad notations *)
Require Export ExtLib.Structures.Monads.
Export MonadNotation. Open Scope monad_scope.

From Coq Require Import List Int BinInt FunInd.
From Coq Require Import Strings.BinaryString.
From Coq Require Import Morphisms.
From Coq Require Import MSets.MSetGenTree.
From Coq Require Import Permutation.

Import BoundedN.Stdpp.

Import LocalBlockchain.
Import ListNotations.
Close Scope address_scope.
Definition AddrSize := (2^8)%N.

Definition LocalChainBase : ChainBase := ChainGens.LocalChainBase.

Definition next_header (chain : ChainBuilder) :=
    {| block_height := S (chain_height chain);
       block_slot := S (current_slot chain);
       block_finalized_height := finalized_height chain;
       block_creator := creator;
       block_reward := 50; |}.

Definition next_header_lc (chain : @LocalChain AddrSize) :=
    {| block_height := S (chain_height chain);
       block_slot := S (current_slot chain);
       block_finalized_height := finalized_height chain;
       block_creator := creator;
       block_reward := 50; |}.

Definition my_add_block c acts := (add_block_exec true c (next_header_lc c) acts).

Open Scope bool_scope.

Section Trees.
  Variable V : Type.
  Variable default: V.
  Definition key := N.
  Inductive tree : Type :=
   | leaf : tree
   | node : V -> tree -> tree -> tree.
  Definition empty_tree : tree := leaf.
End Trees.
Arguments leaf {V}.
Arguments node {V} _ _ _.

Fixpoint allPaths_fix {V : Type} (t : tree V) (acc : list (list V)) : list (list V) :=
let call_rec n v := match acc with
  | [] => allPaths_fix n [[v]]
  | _ => allPaths_fix n (map (fun l => l ++ [v]) acc) 
  end in
match t with
| leaf => acc
| node v 
       (node _ _ _ as l) 
       leaf => call_rec l v
| node v 
       leaf 
       (node _ _ _ as r) => call_rec r v
| node v 
       (node _ _ _ as l) 
       (node _ _ _ as r) => call_rec l v ++ call_rec r v
| node v leaf leaf => (map (fun l => l ++ [v]) acc) 
end.

Definition allPaths {V : Type} (t : tree V) : list (list V):= allPaths_fix t [[]].

Example ex_tree : tree nat := node 1 (node 2 leaf leaf) (node 3 (node 4 leaf leaf) (node 5 leaf leaf)).
(* Compute (show (allPaths ex_tree)). *)

Derive Arbitrary for tree.

Open Scope string_scope.

Instance showTree {A} `{_ : Show A} : Show (tree A) :=
  {| show t := let fix aux (indent : string) t :=
       match t with
         | leaf => "leaf"
         | node x l r =>
                      "(node" ++ nl 
                      ++ indent ++ "(" ++ show x ++ ")" ++ nl
                      ++ indent ++ aux (indent ++ "  ") l ++ nl 
                      ++ indent ++  aux (indent ++ "  ") r ++ ")"
       end
     in nl ++ "Begin Tree:" ++ nl ++ (aux "  " t) ++ nl ++ "End Tree."
  |}.
Close Scope string_scope.

Inductive LocalChainStep {AddrSize : N} : Type :=
| step_add_block : forall (prev_chain : @LocalChain AddrSize) 
                          (header : BlockHeader) 
                          (next_chain : @LocalChain AddrSize), LocalChainStep
| step_action : forall (prev_chain : @LocalChain AddrSize) 
                       (header : BlockHeader) 
                       (next_chain : @LocalChain AddrSize) 
                       (acts : list Action), LocalChainStep.
                       
Definition acts_of_lcstep (state : @LocalChainStep AddrSize) :=
  match state with
  | step_add_block _ _ _ => []
  | step_action _ _ _ acts => acts
  end.
                       
Definition prev_lc_of_lcstep (state : @LocalChainStep AddrSize) :=
  match state with
  | step_add_block prev _ _ => prev
  | step_action prev _ _ _ => prev
  end.

Definition next_lc_of_lcstep (state : @LocalChainStep AddrSize) : LocalChain :=
  match state with
  | step_add_block _ _ next => next
  | step_action _ _ next _ => next
  end.
Close Scope string_scope.
Definition lc_shallow_eqb lc1 lc2 : bool := 
  (lc_height lc1 =? lc_height lc2) 
  && (lc_slot lc1 =? lc_slot lc2) 
  && (@lc_fin_height AddrSize lc1 =? @lc_fin_height AddrSize lc2).


Definition mk_basic_step_add_block c : option (LocalChain * LocalChainStep) := 
  let header := (next_header_lc c) in
  let c_next_opt := add_block_exec false c header [] in
  match c_next_opt with
  | None => None
  | Some c_next => Some (c_next, step_add_block c header c_next)
  end.

Definition mk_basic_step_action c acts : option (LocalChain * LocalChainStep) := 
  let header := (next_header_lc c) in
  let c_next_opt := add_block_exec false c header acts in
  match c_next_opt with
  | Some c_next => Some (c_next, step_action c header c_next acts)
  | None => None
  end.

(* Example t : tree LocalChainStep := node (mk_basic_step_add_block lc_initial) 
              (node (mk_basic_step_action c1 []) leaf leaf)
              leaf. *)
Open Scope string_scope.
Instance showLocalChainStepVerbose : Show LocalChainStep :=
{|
  show step := match step with
  | step_add_block prev header next => 
    "step_add_block{ prev_lc: " ++ show prev ++ sep ++ "header: " ++ show header ++ sep ++ "next_lc:" ++ show next ++ "}"  
  | step_action prev header next acts =>
    "step_action{ prev_lc: " ++ show prev ++ sep ++ "header: " ++ show header ++ sep ++ "next_lc:" ++ show next ++ sep ++ "acts: " ++ show acts ++ "}"
  end
|}.

Instance showLocalChainStep {AddrSize : N} : Show (@LocalChainStep AddrSize) :=
{|
  show step := match step with
  | step_add_block prev header next => 
    "step_add_block{ ... }"  
  | step_action prev header next acts =>
    "step_action{" ++ show acts ++ "}"
  end
|}.

(* Instance showLocalChainStepWithOnlyName {AddrSize : N} : Show (@LocalChainStep AddrSize) :=
{|
  show step := match step with
  | step_add_block prev header next => 
    "step_add_block"  
  | step_action prev header next acts =>
    "step_action"
  end
|}. *)


(* ---------------------- Trace Tree on LocalChain ---------------------- *)

Definition lctracetree := tree (@LocalChainStep AddrSize).


Fixpoint next_lc_eq_child_prev_lc_P (t : lctracetree) := 
  match t with
  | leaf => true
  | node step (node step_lchild lcl lcr) (node step_rchild rcl rcr) =>
    (lc_shallow_eqb (next_lc_of_lcstep step) (prev_lc_of_lcstep step_lchild))
    && (lc_shallow_eqb (next_lc_of_lcstep step) (prev_lc_of_lcstep step_rchild))
  | _ => true 
  end.

Instance showLctracetree : Show lctracetree :=
{|
  show t := @show _ (@showTree _ showLocalChainStep) t 
|}.


Fixpoint glctracetree_fix (prev_lc : LocalChain)
                          (gActOptFromLCSized : LocalChain -> nat -> G (option Action))
                          (height : nat) : G lctracetree :=
  match height with
  | 0 | 1 => returnGen leaf
  | S height => 
    lc_opt <- backtrack [
      (10, 
          (* acts <- liftM (shrinkListTo 2) (optToVector 5 (gActOptFromLCSized prev_lc 2)) ;; *)
          bindGenOpt (gActOptFromLCSized prev_lc 2)
          (fun act => returnGen (mk_basic_step_action prev_lc [act]))
      )
          (* match acts with
          | [] => returnGen None
          | _ => returnGen (mk_basic_step_action prev_lc acts)
          end) *)
      (* (1, returnGen (mk_basic_step_add_block prev_lc)) ; *)
      (* (3, liftM (mk_basic_step_action prev_lc ) (optToVector 1 (gDeployCongressActionFromLC prev_lc)))  *)
      ] ;;
    match lc_opt with
          | Some (lc, step) => 
            liftM2 (node step) 
                   (glctracetree_fix lc gActOptFromLCSized height) 
                   (glctracetree_fix lc gActOptFromLCSized height) 
          | None => returnGen leaf
    end
  end.


(* QuickChick (forAll (glctracetree 7) next_lc_eq_child_prev_lc_P). *)
(* coqtop-stdout:+++ Passed 10000 tests (0 discards) *)


Fixpoint gLocalChainTraceList_fix (prev_lc : LocalChain)
                              (gActOptFromLCSized : LocalChain -> nat -> G (option Action))
                              (length : nat)
                              (max_nr_acts_per_block : nat) 
                              : G (list LocalChainStep) :=
  match length with
  | 0 => returnGen []
  | S length => 
    lc_opt <- backtrack [
      (10, 
          (* What we're essentially doing here trying twice and then discarding one - to increase robustness.  *)
          let try_twice g := backtrack [(1, g);(1, g)] in
          try_twice (
            acts <- optToVector max_nr_acts_per_block (gActOptFromLCSized prev_lc 2) ;;
            returnGen (mk_basic_step_action prev_lc acts)
          )
          (* acts <- liftM (shrinkListTo 1) (optToVector nr_retries ) ;; *)
          (* returnGen (mk_basic_step_action prev_lc acts) *)
          (* bindGenOpt (gActOptFromLCSized prev_lc 2) *)
          (* (fun act => returnGen (mk_basic_step_action prev_lc [act])) *)
      )
          (* match acts with
          | [] => returnGen None
          | _ => returnGen (mk_basic_step_action prev_lc acts)
          end) *)
      (* (1, returnGen (mk_basic_step_add_block prev_lc)) ; *)
      (* (3, liftM (mk_basic_step_action prev_lc ) (optToVector 1 (gDeployCongressActionFromLC prev_lc)))  *)
      ] ;;
    match lc_opt with
          | Some (lc, step) => 
            liftM (cons step) 
                   (gLocalChainTraceList_fix lc gActOptFromLCSized length max_nr_acts_per_block) 
          | None => returnGen []
    end
  end.

Open Scope string_scope.
Instance showLocalChainList {AddrSize : N}: Show (list (@LocalChainStep AddrSize)) :=
{|
  show l := nl ++ "Begin Trace: " ++ nl ++ String.concat (";;" ++ nl) (map show l) ++ nl ++ "End Trace"
|}.
Close Scope string_scope.  

Fixpoint all_suffices_fix {A : Type} (l : list A) (acc : list (list A)) : list (list A) := 
  match l with
  | [] => acc
  | x::xs => match acc with
             | [] => all_suffices_fix xs [[x]]
             | _ => all_suffices_fix xs ([x] :: (map (fun l => app l [x]) acc)) 
             end
  end.

(* TODO: pretty ugly solution. Maybe fix. *)
Definition all_prefixes {A : Type} (l : list A) := map (fun l => rev' l) (all_suffices_fix (rev' l) []).
Compute (all_prefixes [1;2;3;4]).


(* -------------------- Checker combinators on traces --------------------  *)

(* Checks that a property holds on all states in all traces from a given trace generator *)
Definition forAllTraces {prop : Type}
                       `{Checkable prop}
                        {AddrSize : N}
                        (maxLength : nat)
                        (init_lc : @LocalChain AddrSize)
                        (gTrace : LocalChain -> nat -> G (list LocalChainStep))
                        (pf : LocalChain -> prop)
                        : Checker :=
  forAll (gTrace init_lc maxLength) 
  (fun trace => conjoin (map (checker o pf o next_lc_of_lcstep) trace))
.

(* A variant where the property is over the whole trace *)
Definition forAllTraces_traceProp {prop : Type}
                       `{Checkable prop}
                        {AddrSize : N}
                        (maxLength : nat)
                        (init_lc : LocalChain)
                        (gTrace : (@LocalChain AddrSize) -> nat -> G (list (@LocalChainStep AddrSize)))
                        (pf : list LocalChainStep -> prop)
                        : Checker :=
  forAll (gTrace init_lc maxLength)  pf.


Definition reachableFromSized {AddrSize : N}
                         (maxLength : nat) 
                         (init_lc : (@LocalChain AddrSize))
                         (gTrace : LocalChain -> nat -> G (list LocalChainStep))
                         (pf : @LocalChainStep AddrSize -> bool)
                         : Checker := 
  existsP (gTrace init_lc maxLength) (fun trace => existsb pf trace).

Definition reachableFrom {AddrSize : N} init_lc gTrace pf : Checker := 
  sized (fun n => @reachableFromSized AddrSize n init_lc gTrace pf).


(* A variant where instead of having an initial state, we just have an initial predicate on a state *)
Definition reachableFrom_propSized {AddrSize : N}
                                   (maxLength : nat) 
                                   (init_lc : (@LocalChain AddrSize))
                                   (gTrace : LocalChain -> nat -> G (list LocalChainStep))
                                   (pf : LocalChain -> bool)
                                   : Checker := 
  existsP 
    (gTrace init_lc maxLength) 
    (fun trace => existsb pf (map (next_lc_of_lcstep) trace)).



Fixpoint cut_at_first_satisfying_fix {A : Type} (p : A -> bool) (l : list A) (acc : list A) : option (list A) :=
  match l with
  | [] => None
  | x::xs => if p x 
             then Some (acc ++ [x])
             else (cut_at_first_satisfying_fix p xs (acc ++ [x]))
  end.

Definition cut_at_first_satisfying_ {A : Type} (p : A -> bool) (l : list A) := cut_at_first_satisfying_fix p l [] .

(* represents: if there is a state x, satisfying pf1, reachable from init_lc,
               then there is a state y, satisfyring pf2, reachable from state x. *)
Definition reachableFrom_implies_reachableSized
                         (maxLength : nat) 
                         (init_lc : (@LocalChain AddrSize))
                         (gTrace : @LocalChain AddrSize -> nat -> G (list (@LocalChainStep AddrSize)))
                         (pf1 : LocalChain -> bool)
                         (pf2 : LocalChain -> bool)
                         : Checker := 
  expectFailure (forAll (gTrace init_lc maxLength)  
    (fun trace =>
     match cut_at_first_satisfying_ (pf1 o next_lc_of_lcstep) trace with
      | None => checker true
      | Some trace_cut => 
        let new_init_lc := (List.last (map next_lc_of_lcstep trace_cut) init_lc) in
        expectFailure (forAll (gTrace new_init_lc maxLength) 
        (fun new_trace => whenFail 
          ("Success - found witnesses satisfying the predicates:" ++ nl ++
          "First trace:"  ++
          show trace_cut ++ nl ++ 
          "Second trace:" ++
          show new_trace ++ nl)
          ((checker o negb) (existsb pf2 (map (next_lc_of_lcstep) new_trace)))
        ))
      end)).

Definition reachableFrom_implies_reachable init_lc gTrace pf1 pf2 : Checker := 
  sized (fun n => reachableFrom_implies_reachableSized n init_lc gTrace pf1 pf2).




(* If a state satisfying pf1 is reachable from init_lc, then any trace from this state satisfies pf_trace  *)
Definition reachableFrom_implies_tracePropSized
                         {A prop : Type}
                        `{Checkable prop}
                         (maxLength : nat) 
                         (init_lc : (@LocalChain AddrSize))
                         (gTrace : @LocalChain AddrSize -> nat -> G (list (@LocalChainStep AddrSize)))
                         (pf1 : LocalChainStep -> option A)
                         (pf_trace : A -> list LocalChainStep -> prop)
                         : Checker := 
  forAll (gTrace init_lc maxLength)  
  (fun trace =>
    let pf1_bool lc := match pf1 lc with Some _ => true | None => false end in 
    match cut_at_first_satisfying_ pf1_bool trace with
    | Some (x::xs as trace_cut) => 
      let last_step := (List.last trace_cut x) in
      isSomeCheck (pf1 last_step)
        (fun a =>
          let new_init_lc := next_lc_of_lcstep last_step in
          (forAll (gTrace new_init_lc maxLength) 
            (fun new_trace => (pf_trace a new_trace))
          )
        )
    | Some [] => checker false
    | _ => false ==> true
    end).

Definition reachableFrom_implies_traceProp {A : Type}
                                           (init_lc : (@LocalChain AddrSize))
                                           (gTrace : @LocalChain AddrSize -> nat -> G (list (@LocalChainStep AddrSize)))
                                           (pf1 : LocalChainStep -> option A)
                                           (pf_trace : A -> list LocalChainStep -> bool)
                                           : Checker := 
  sized (fun n => reachableFrom_implies_tracePropSized n init_lc gTrace pf1 pf_trace).


Fixpoint split_at_first_satisfying_fix {A : Type} (p : A -> bool) (l : list A) (acc : list A) : option (list A * list A) :=
  match l with
  | [] => None
  | x::xs => if p x 
             then Some (acc ++ [x], xs)
             else (split_at_first_satisfying_fix p xs (acc ++ [x]))
  end.

Definition split_at_first_satisfying {A : Type} (p : A -> bool) (l : list A) : option (list A * list A) :=
  split_at_first_satisfying_fix p l [].

Compute (split_at_first_satisfying (fun x => x =? 2) [1;3;2;4;5]).

Definition reachableFrom_implies_tracePropSized_new
                         {A prop : Type}
                        `{Checkable prop}
                         (maxLength : nat) 
                         (init_lc : (@LocalChain AddrSize))
                         (gTrace : @LocalChain AddrSize -> nat -> G (list (@LocalChainStep AddrSize)))
                         (pf1 : LocalChainStep -> option A)
                         (pf_trace : A -> list LocalChainStep -> list LocalChainStep -> prop)
                         : Checker := 
  forAll (gTrace init_lc maxLength) 
  (fun trace =>
    let pf1_bool := isSome o pf1 in 
    match split_at_first_satisfying pf1_bool trace with
    | Some ((x::xs) as pre, (y::ys) as post) =>
      let last_step := (List.last pre x) in
      isSomeCheck (pf1 last_step) 
        (fun a => (pf_trace a pre post))
    | _ => false ==> true
    end).