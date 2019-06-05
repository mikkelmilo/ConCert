(* Distributed under the terms of the MIT license.   *)

From Coq Require Import Bool String List Program BinPos Compare_dec Omega.
From Template Require Import config utils Ast univ Induction LiftSubst UnivSubst Typing.
From Template Require Import AstUtils.
Require Import Facts CustomTactics.
Require Import String.
Local Open Scope string_scope.
Set Asymmetric Patterns.

Existing Instance default_checker_flags.

(** * Weak (head) call-by-value evaluation strategy.

  The [wcbveval] inductive relation specifies weak cbv evaluation.  It
  is shown to be a subrelation of the 1-step reduction relation from
  which conversion is defined. Hence two terms that reduce to the same
  wcbv head normal form are convertible.

  This reduction strategy is supposed to mimick at the Coq level the
  reduction strategy of ML programming languages. It is used to state
  the extraction conjecture that can be applied to Coq terms to produce
  (untyped) terms where all proofs are erased to a dummy value. *)

(** ** Big step version of weak cbv beta-zeta-iota-fix-delta reduction.

  TODO: CoFixpoints *)

(* We define a notion of atom for terms that reduce to themselves, when
   they are not applied.

   We do not include [Rel] which is handled specially, [Var] and [Meta]
   which are out of scope. We assume no axioms either, that is constants
   with no bodies.

*)

Definition atom t :=
  match t with
  | tSort _
  | tInd _ _
  | tConstruct _ _ _
  | tFix _ _
  | tCoFix _ _ => true
  | _ => false
  end.

Definition mkApps' (t : term) (ts : list term):=
  match ts with
  | [] => t
  | _ => tApp t ts
  end.


Fixpoint flat_apps (t  : term) : bool :=
  match t  with
  | tRel x => true
  | tVar x => true
  | tMeta x => true
  | tEvar x x0 => true
  | tSort x => true
  | tCast t1 _ t2 => flat_apps t1 && flat_apps t2
  | tProd _ t1 t2 => flat_apps t1 && flat_apps t2
  | tLambda _ t1 t2 => flat_apps t1 && flat_apps t2
  | tLetIn nm t1 t2 t3 => flat_apps t1 && flat_apps t2 && flat_apps t3
  | tApp t ts => negb (isApp t) && forallb flat_apps ts
  | tConst _ _ => true
  | tInd _ _ => true
  | tConstruct _ _ _ => true
  | tCase _ t1 t2 bs => flat_apps t1 && flat_apps t2 && forallb (test_snd (flat_apps)) bs
  | tProj _ t => flat_apps t
  | tFix mfx _ => forallb (test_def flat_apps) mfx
  | tCoFix mfx _ => forallb (test_def flat_apps) mfx
  end.


Lemma lift_flat_apps t n m :
  flat_apps t -> flat_apps (lift n m t ).
Proof.
Admitted.

Hint Resolve <- negb_true_iff : facts.
Hint Resolve -> negb_true_iff : facts.

Lemma flat_apps_no_apps t t1 ts :
  flat_apps t -> t = tApp t1 ts -> isApp t1 = false /\ forallb flat_apps ts = true.
Proof.
  intros Happ Heq. subst. simpl in *. inv_andb Happ;split;eauto with facts.
Qed.

Lemma subst_flattens t u n:
  flat_apps u ->
  flat_apps (t{n:=u}).
Proof.
  revert u n.
  induction t using Induction.term_forall_list_ind;simpl;intros u1 n1 Hu1;eauto.
  + destruct (n1 ?= n);auto. now apply lift_flat_apps.
  + split_andb. now apply IHt1. now apply IHt2.
  + split_andb. now apply IHt1. now apply IHt2.
  + split_andb. now apply IHt1. now apply IHt2.
  + repeat split_andb. now apply IHt1. now apply IHt2.  now apply IHt3.
  + destruct l.
    * simpl. easy.
    * inversion H as [a | a b Ht0 Hfa];subst;clear H.
      destruct (isApp (t {n1 := u1})) eqn:Ht.
      ** destruct (t {n1 := u1}) eqn:Htsubst;auto;inversion Ht.
         assert (flat_apps (t {n1 := u1})) by easy.
         simpl in *.
         unfold is_true.
         assert (Happ : isApp t1 = false /\ forallb flat_apps l0 = true).
         { eapply flat_apps_no_apps;eauto. }
         destruct Happ. split_andb;eauto with facts.
         rewrite forallb_app. split_andb;eauto with facts.
         simpl. split_andb. apply Ht0;easy.
         rewrite forallb_map.
         eapply Forall_forallb;eauto.
      ** rewrite mkApps_tApp. simpl.
         split_andb;eauto with facts.
         split_andb. now apply Ht0.
         rewrite forallb_map.
         eapply Forall_forallb;eauto. intros H;tryfalse.
         intros H;tryfalse.
  +
Admitted.


Section Wcbv.
  Context (Σ : global_declarations) (Γ : context).
  (* The local context is fixed: we are only doing weak reductions *)

  Inductive eval : term -> term -> Prop :=
  (** Reductions *)
  (** Beta *)
  | eval_beta t a l res :
      eval_apps t (a :: l) res ->
      eval (tApp t (a :: l)) res

  (** Let *)
  | eval_zeta na b0 b0' t b1 res :
      eval b0 b0' ->
      eval (subst0 b0' b1) res ->
      eval (tLetIn na b0 t b1) res

  (** Local variables: defined or undefined *)
  | eval_rel_def i (isdecl : i < List.length Γ) body res :
      (safe_nth Γ (exist _ i isdecl)).(decl_body) = Some body ->
      eval (lift0 (S i) body) res ->
      eval (tRel i) res

  | eval_rel_undef i (isdecl : i < List.length Γ) :
      (safe_nth Γ (exist _ i isdecl)).(decl_body) = None ->
      eval (tRel i) (tRel i)

  (** Case *)
  | eval_iota ind pars discr c u args p brs res :
      eval discr (mkApps (tConstruct ind c u) args) ->
      eval (iota_red pars c args brs) res ->
      eval (tCase (ind, pars) p discr brs) res

  (** Constant unfolding *)
  | eval_delta c decl body (isdecl : declared_constant Σ c decl) u res :
      decl.(cst_body) = Some body ->
      eval (subst_instance_constr u body) res ->
      eval (tConst c u) res

  (** Proj *)
  | eval_proj i pars arg discr args k u res :
      eval discr (mkApps (tConstruct i k u) args) ->
      eval (List.nth (pars + arg) args tDummy) res ->
      eval (tProj (i, pars, arg) discr) res

  (* TODO CoFix *)
  | eval_abs na M N : eval (tLambda na M N) (tLambda na M N)

  | eval_prod na b t : eval (tProd na b t) (tProd na b t)

  | eval_atom t : atom t = true -> eval t t

  | eval_evar ev l : eval (tEvar ev l) (tEvar ev l) (* Lets say it is a value for now *)

  | eval_cast M1 k M2 N1 : eval M1 N1 -> eval (tCast M1 k M2) N1
  with
  eval_apps : term -> list term -> term -> Prop :=
  | eval_app_lam f na t b a a' l res :
      eval f (tLambda na t b) ->
      eval a a' ->
      eval_apps (subst0 a' b) l res ->
      eval_apps f (a :: l) res
  | eval_app_empty t res :
      eval t res ->
      eval_apps t [] res
  | eval_app_constr a f i k u l l' :
      eval f (tConstruct i k u) ->
      All2 eval (a :: l) l' ->
      eval_apps f (a :: l) (tApp (tConstruct i k u) l')
  | eval_app_ind a t i u l l' :
      eval t (tInd i u) ->
      All2 eval (a :: l) l' ->
      eval_apps t (a :: l) (tApp (tInd i u) l')

    (** Fix unfolding, with guard *)
  | eval_fix mfix idx args args' narg fn res :
      unfold_fix mfix idx = Some (narg, fn) ->
      All2 eval args args' -> (* FIXME should we reduce the args after the recursive arg here? *)
      is_constructor narg args' = true ->
      eval_apps fn args' res ->
      eval_apps (tFix mfix idx) args res.

  (* | eval_fix mfix idx args args' a narg fn res l : *)
  (*     unfold_fix mfix idx = Some (narg, fn) -> *)
  (*     All2 eval args args' -> (* FIXME should we reduce the args after the recursive arg here? *) *)
  (*     is_constructor 0 [a] = true -> *)
  (*     eval_apps fn args' res -> *)
  (*     eval_apps (tFix (mkdef nm dty dbody 0) idx) (a :: l) res. *)


  (** The right induction principle for the nested [Forall] cases: *)

  Lemma eval_evals_ind :
    forall P : term -> term -> Prop,
      (forall (f : term) (na : name) (t b a a' : term) (l : list term) (res : term),
          eval f (tLambda na t b) ->
          P f (tLambda na t b) ->
          eval a a' -> P a a' ->
          eval (mkApps' (b {0 := a'}) l) res -> P (mkApps (b {0 := a'}) l) res -> P (tApp f (a :: l)) res) ->

      (forall (na : name) (b0 b0' t b1 res : term),
          eval b0 b0' -> P b0 b0' -> eval (b1 {0 := b0'}) res -> P (b1 {0 := b0'}) res -> P (tLetIn na b0 t b1) res) ->

      (forall (i : nat) (isdecl : i < #|Γ|) (body res : term),
          decl_body (safe_nth Γ (exist (fun n : nat => n < #|Γ|) i isdecl)) = Some body ->
          eval ((lift0 (S i)) body) res -> P ((lift0 (S i)) body) res -> P (tRel i) res) ->

      (forall (i : nat) (isdecl : i < #|Γ|),
          decl_body (safe_nth Γ (exist (fun n : nat => n < #|Γ|) i isdecl)) = None -> P (tRel i) (tRel i)) ->

      (forall (ind : inductive) (pars : nat) (discr : term) (c : nat) (u : universe_instance)
              (args : list term) (p : term) (brs : list (nat * term)) (res : term),
          eval discr (mkApps (tConstruct ind c u) args) ->
          P discr (mkApps (tConstruct ind c u) args) ->
          eval (iota_red pars c args brs) res ->
          P (iota_red pars c args brs) res -> P (tCase (ind, pars) p discr brs) res) ->

      (forall (mfix : mfixpoint term) (idx : nat) (args args' : list term) (narg : nat) (fn res : term),
          unfold_fix mfix idx = Some (narg, fn) ->
          All2 eval args args' ->
          All2 P args args' ->
          is_constructor narg args' = true ->
          eval (mkApps fn args') res -> P (mkApps fn args') res -> P (tApp (tFix mfix idx) args) res) ->

      (forall (c : ident) (decl : constant_body) (body : term),
          declared_constant Σ c decl ->
          forall (u : universe_instance) (res : term),
            cst_body decl = Some body ->
            eval (subst_instance_constr u body) res -> P (subst_instance_constr u body) res -> P (tConst c u) res) ->

      (forall (i : inductive) (pars arg : nat) (discr : term) (args : list term) (k : nat)
              (u : universe_instance) (res : term),
          eval discr (mkApps (tConstruct i k u) args) ->
          P discr (mkApps (tConstruct i k u) args) ->
          eval (nth (pars + arg) args tDummy) res ->
          P (nth (pars + arg) args tDummy) res -> P (tProj (i, pars, arg) discr) res) ->

      (forall (na : name) (M N : term), P (tLambda na M N) (tLambda na M N)) ->

      (forall (na : name) (M N : term), P (tProd na M N) (tProd na M N)) ->

      (forall (f8 : term) (i : inductive) (u : universe_instance) (l l' : list term),
          l <> nil -> eval f8 (tInd i u) ->
          P f8 (tInd i u) -> All2 eval l l' -> All2 P l l' -> P (tApp f8 l) (tApp (tInd i u) l')) ->

      (forall (f8 : term) (i : inductive) (k : nat) (u : universe_instance) (l l' : list term),
          l <> nil -> eval f8 (tConstruct i k u) ->
          P f8 (tConstruct i k u) -> All2 eval l l' -> All2 P l l' -> P (tApp f8 l) (tApp (tConstruct i k u) l')) ->

      (forall (t : term), atom t = true -> P t t) ->

      (forall (ev : nat) (l : list term), P (tEvar ev l) (tEvar ev l)) ->

      (forall (M1 : term) (k : cast_kind) (M2 N1 : term), eval M1 N1 -> P M1 N1 -> P (tCast M1 k M2) N1) ->

      forall t t0 : term, eval t t0 -> P t t0.
  Proof.
    intros P Hbeta Hlet Hreldef Hrelvar Hcase Hfix Hconst Hproj Hlam Hprod Hindapp Hcstrapp Hatom Hevar Hcast.
    fix eval_evals_ind 3. destruct 1;
             try match goal with [ H : _ |- _ ] =>
                             match type of H with
                             | forall t t0, eval t t0 -> _ => fail 1
                             | context [ atom _ ] => fail 1
                             | _ => eapply H
                             end end; eauto.
    (* clear H1. *)
  (*   (* clear H2. *) *)
  (*   revert args args' H0. fix aux 3. destruct 1.  constructor; auto. *)
  (*   constructor. now apply eval_evals_ind. now apply aux. *)
  (*   revert l l' H H1. fix aux 4. destruct 2. contradiction. constructor. *)
  (*   now apply eval_evals_ind. *)
  (*   destruct l. inv H1; constructor. *)
  (*   now apply aux. *)
  (*   revert l l' H H1. fix aux 4. destruct 2. contradiction. constructor. *)
  (*   now apply eval_evals_ind. destruct l. inv H1; constructor. now apply aux. *)
    (* Defined. *)
  Admitted.

  (** Characterization of values for this reduction relation:
      Basically atoms (constructors, inductives, products (FIXME sorts missing))
      and de Bruijn variables and lambda abstractions. Closed values disallow
      de Bruijn variables. *)

  Inductive value : term -> Prop :=
  | value_tRel i : value (tRel i)
  | value_tEvar ev l : value (tEvar ev l)
  | value_tLam na t b : value (tLambda na t b)
  | value_tProd na t u : value (tProd na t u)
  | value_tInd i k l : All value l -> value (mkApps (tInd i k) l)
  | value_tConstruct i k u l : All value l -> value (mkApps (tConstruct i k u) l)
  | value_atom t : atom t = true -> value t.

  Lemma value_values_ind : forall P : term -> Prop,
       (forall i : nat, P (tRel i)) ->
       (forall (ev : nat) (l : list term), P (tEvar ev l)) ->
       (forall (na : name) (t b : term), P (tLambda na t b)) ->
       (forall (na : name) (t u : term), P (tProd na t u)) ->
       (forall (i : inductive) (k : universe_instance) l,
           All value l ->
           All P l -> P (mkApps (tInd i k) l)) ->
       (forall (i : inductive) (k : nat) (u : universe_instance) (l : list term),
        All value l -> All P l -> P (mkApps (tConstruct i k u) l)) ->
       (forall t, atom t = true -> P t) ->
       forall t : term, value t -> P t.
  Proof.
    intros P ???????.
    fix value_values_ind 2. destruct 1. 1-4:clear value_values_ind; auto.
    apply H3. auto.
    revert l H6. fix aux 2. destruct 1. constructor; auto.
    constructor. now apply value_values_ind. now apply aux.
    apply H4. apply H6.
    revert l H6. fix aux 2. destruct 1. constructor; auto.
    constructor. now apply value_values_ind. now apply aux.
    now apply H5.
  Defined.

  (** The codomain of evaluation is only values:
      It means no redex can remain at the head of an evaluated term. *)

  Lemma eval_to_value e e' : eval e e' -> value e'.
  Proof.
    induction 1 using eval_evals_ind; simpl; auto using value.
    pose (value_tInd i u l'). apply All2_right in H2.
    rewrite mkApps_tApp in v; auto. simpl; auto. eauto using All2_non_nil.
    pose proof (value_tConstruct i k u l'). forward H3.
    apply (All2_right H2).
    rewrite mkApps_tApp in H3; auto. simpl; auto. eauto using All2_non_nil.
  Qed.

  (** Evaluation preserves closedness: *)
  Lemma eval_closed : forall n t u, closedn n t = true -> eval t u -> closedn n u = true.
  Proof.
    induction 2 using eval_evals_ind; simpl in *; eauto 2. eapply IHeval3.
    admit.
    eapply IHeval2.
  Admitted. (* FIXME complete *)

End Wcbv.

(** Well-typed closed programs can't go wrong: they always evaluate to a value. *)

Conjecture closed_typed_wcbeval : forall (Σ : global_context) t T,
    Σ ;;; [] |- t : T -> { u & eval (fst Σ) [] t u }.

(** Evaluation is a subrelation of reduction: *)

Lemma wcbeval_red : forall (Σ : global_declarations) Γ t u,
    eval Σ Γ t u -> red Σ Γ t u.
Proof.
  induction 1; try constructor; eauto.
Admitted. (** TODO: Congruence lemmas of red for all constructions (as done in Coq in Coq) *)