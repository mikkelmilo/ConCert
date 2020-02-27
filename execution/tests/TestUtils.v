Require Import ZArith Strings.Ascii Strings.String.
From QuickChick Require Import QuickChick. Import QcNotation.
From ExtLib.Structures Require Import Functor Applicative.
Require Export ExtLib.Structures.Monads.
Export MonadNotation. Open Scope monad_scope.

From ConCert Require Import Blockchain.
From ConCert Require Import LocalBlockchain.
From ConCert Require Import Serializable. Import SerializedType.
From ConCert Require Import BoundedN ChainedList.



From Coq Require Import List. Import ListNotations.
From Coq Require Import Program.Basics.
Require Import Containers.

Global Definition AddrSize := (2^8)%N.
Instance LocalChainBase : ChainBase := LocalChainBase AddrSize.
Instance LocalChainBuilder : ChainBuilderType := LocalChainBuilderDepthFirst AddrSize.

Notation "f 'o' g" := (compose f g) (at level 50).


(* Misc utility functions *)
Open Scope list_scope.
Open Scope string_scope.

Fixpoint mkMapFromLists {A B : Type}
                       (a_eqb : A -> A -> bool)
                       (default : B)
                       (l : list A) 
                       (lb : list B)
                       : A -> B :=
  match (l,lb) with
  | ([],[]) => fun x => default
  | (a::l', b::lb') => 
    fun (x : A) => if a_eqb x a then b else (mkMapFromLists a_eqb default l' lb') x 
  | (_,_) => fun x => default
  end.

Definition string_of_FMap {A B : Type}
                         `{countable.Countable A}
                         `{base.EqDecision A}
                          (showA : A -> string) 
                          (showB : B -> string) 
                          (m : FMap A B) : string :=
  show (map (fun p => showA (fst p) ++ "-->" ++ showB (snd p)) (FMap.elements m)).


(* Utils for Show instances *)

Definition empty_str : string := "".
Definition sep : string := ", ".
Derive Show for unit.

Definition deserialize_to_string (s : SerializedValue) : string := 
  match deserialize s with
  | Some v => show v
  | None => "?"
  end.

Instance showFMap {A B : Type}
                 `{countable.Countable A}
                 `{base.EqDecision A}
                 `{Show A} 
                 `{Show B}
                  : Show (FMap A B) :=
{|
  show := string_of_FMap show show
|}.

Close Scope string_scope.


(* Utils for Generators *)


Record ChainContext (BaseTypes : ChainBase) := 
  mkBaseGens {
    gAddress              : G (@Address BaseTypes);
    accounts              : list (@Address BaseTypes);
    contracts             : list (@Address BaseTypes);
    gContractAddr         : G (@Address BaseTypes);
    gAccountAddr          : G (@Address BaseTypes);    
  }.
  
(* Helpers for ChainContext. TODO: look into parameterising ChainBase *)
Definition ctx_gAccountAddr (ctx : ChainContext LocalChainBase) : G (@Address LocalChainBase) := 
  @gAccountAddr LocalChainBase ctx.
Definition ctx_gContractAddr (ctx : ChainContext LocalChainBase) : G (@Address LocalChainBase) := 
  @gContractAddr LocalChainBase ctx.
Definition ctx_gAnyAddr (ctx : ChainContext LocalChainBase) : G (@Address LocalChainBase) := 
  @gAddress LocalChainBase ctx.
Definition ctx_accounts (ctx : ChainContext LocalChainBase) : list Address := 
  @accounts LocalChainBase ctx.
Definition ctx_contracts (ctx : ChainContext LocalChainBase) : list Address := 
  @contracts LocalChainBase ctx.

Definition gZPositive := liftM Z.of_nat arbitrary.
Definition gZPositiveSized n := liftM Z.of_nat (arbitrarySized n).

(* Helper generator and show instance for arbitrary FMaps *)

Fixpoint gFMapSized {A B : Type} 
                    {gA : G A} 
                    {gB : G B}
                    `{countable.Countable A}
                    `{base.EqDecision A}
                     (n : nat) : G (FMap A B) :=
  match n with
  | 0 => returnGen FMap.empty
  | S n' =>
    a <- gA ;;
    b <- gB ;;
    m <- @gFMapSized _ _ gA gB _ _ _ n' ;;
    returnGen (FMap.add a b m)  
  end.

Fixpoint gFMapFromInput {A B : Type}
                       `{countable.Countable A}
                       `{base.EqDecision A}     
                        (l1 : list A)
                        (l2 : list B)
                        : G (FMap A B) :=
  match (l1, l2) with
  | (a::l1', b::l2') => liftM (FMap.add a b) (gFMapFromInput l1' l2')
  | (_, _) => returnGen FMap.empty
  end.

Instance genFMapSized {A B : Type} 
                     `{Gen A} 
                     `{Gen B}
                     `{countable.Countable A}
                     `{base.EqDecision A}
                      : GenSized (FMap A B) :=
{|
  arbitrarySized := @gFMapSized A B arbitrary arbitrary _ _ _
|}.

Sample (@gFMapSized nat nat arbitrary arbitrary _ _ _ 1).


Fixpoint vectorOfCount {A : Type}
                      `{countable.Countable A} 
                       (default : A)
                       (n : nat) : G (list A) := 
  match n with
  | 0    => returnGen []
  | S n' => 
    match (countable.decode o Pos.of_nat) n with
    | Some a => liftM (cons a) (vectorOfCount default n')
    | None => liftM (cons default) (vectorOfCount default n')
    end
  end.



Fixpoint gInterp_type (t : SerializedType) : G (interp_type t) := 
  match t with
  | ser_unit => returnGen tt
  | ser_int => @arbitrary Z _
  | ser_bool => arbitrary
  | ser_pair a b => liftM2 pair (gInterp_type a) (gInterp_type b) 
  | ser_list a => listOf (gInterp_type a)
  end.

Derive Arbitrary for SerializedType.

Definition gSerializedValueSized (n : nat): G SerializedValue :=
  t <- arbitrarySized n ;;
  liftM (build_ser_value t) (gInterp_type t).

Instance genSerializedValueSized : GenSized SerializedValue :=
{|
  arbitrarySized := gSerializedValueSized 
|}.


(* Utils for QuickChick *)


(* Helper functions when we want to state a property forAll x y z ... (someProp x y z ...) in QuickChick *)
(* Where the generator for y depends on x, the generator for z depends on y, etc. *)
(* Example: In vanilla QC, we have: *)
(* QuickChick (
  forAll
    (gLocalChainContext 2)
    (fun ctx => 
  forAll
    (gLocalChainSized 2 ctx)
    (fun chain => 
  forAll
    (@gStateSized ctx 2)
    (fun state => 
  forAll
    (gChainActionsFromCongressActions ctx)
    (fun cacts => add_proposal_cacts_P cacts chain state
    ))))
). *)
(* Which is of course very clunky. With forAll4 we get: *)
(* QuickChick (
  forAll4
    (gLocalChainContext 2)
    (fun ctx => gLocalChainSized 2 ctx)
    (fun ctx _ => @gStateSized ctx 2)
    (fun ctx _ _ => gChainActionsFromCongressActions ctx)
    (fun ctx chain state cacts => add_proposal_cacts_P cacts chain state)
). *)
(* Which is better, although not optimal. *)
Definition forAll2 {A B prop : Type} 
                  `{Checkable prop} 
                  `{Show A} 
                  `{Show B} 
                   (genA : G A)
                   (fgenB : A -> G B)
                   (pf : A -> B -> prop) :=
  forAll genA (fun a => forAll (fgenB a) (fun b => pf a b)).

Definition forAll3 {A B C prop : Type} 
                  `{Checkable prop} 
                  `{Show A} 
                  `{Show B} 
                  `{Show C} 
                   (genA : G A)
                   (fgenB : A -> G B)
                   (fgenC : A -> B -> G C)
                   (pf : A -> B -> C -> prop) :=
  forAll 
    genA 
    (fun a => 
  forAll 
    (fgenB a) 
  (fun b =>
  forAll
    (fgenC a b)
  (fun c => pf a b c))).

Definition forAll4 {A B C D prop : Type} 
                  `{Checkable prop} 
                  `{Show A} 
                  `{Show B} 
                  `{Show C} 
                  `{Show D} 
                   (genA : G A)
                   (fgenB : A -> G B)
                   (fgenC : A -> B -> G C)
                   (fgenD : A -> B -> C -> G D)
                   (pf : A -> B -> C -> D -> prop) :=
  forAll3 genA fgenB fgenC
    (fun a b c => 
    (forAll
      (fgenD a b c)
      (fun d => pf a b c d))).

Definition forAll5 {A B C D E prop : Type} 
                  `{Checkable prop} 
                  `{Show A} 
                  `{Show B} 
                  `{Show C} 
                  `{Show D} 
                  `{Show E} 
                   (genA : G A)
                   (fgenB : A -> G B)
                   (fgenC : A -> B -> G C)
                   (fgenD : A -> B -> C -> G D)
                   (fgenE : A -> B -> C -> D -> G E)
                   (pf : A -> B -> C -> D -> E -> prop) :=
  forAll4 genA fgenB fgenC fgenD
    (fun a b c d => 
    (forAll
      (fgenE a b c d)
      (fun e => pf a b c d e))).

(* Similar to above, but where the "quantified" variables are not dependent on each other.
   This easens the syntactic form. *)

Definition indepForAll2 {A B prop : Type} 
                       `{Checkable prop} 
                       `{Show A} 
                       `{Show B} 
                        (genA : G A)
                        (genB : G B)
                        (pf : A -> B -> prop) 
                        := forAll2 genA (fun _ => genB) pf.


Definition indepForAll3 {A B C prop : Type} 
                       `{Checkable prop} 
                       `{Show A} 
                       `{Show B} 
                       `{Show C} 
                        (genA : G A)
                        (genB : G B)
                        (genC : G C)
                        (pf : A -> B -> C -> prop) 
                        := forAll3 
                            genA 
                            (fun _ => genB) 
                            (fun _ _ => genC)
                            pf.

Definition indepForAll4 {A B C D prop : Type} 
                       `{Checkable prop} 
                       `{Show A} 
                       `{Show B} 
                       `{Show C} 
                       `{Show D} 
                        (genA : G A)
                        (genB : G B)
                        (genC : G C)
                        (genD : G D)
                        (pf : A -> B -> C -> D -> prop) 
                        := forAll4 
                            genA 
                            (fun _ => genB) 
                            (fun _ _ => genC)
                            (fun _ _ _ => genD)
                            pf.

(* Little helper to avoid having to write out matches with "false ==> true" in None case all the time *)
Definition isSomeCheck {A B : Type} `{Checkable B} (a : option A) (f : A -> B) : Checker := 
  match a with
  | Some v => checker (f v)
  | None => false ==> true
end.