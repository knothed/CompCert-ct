Require Import Common Coqlib Classical Datatypes.
Require Import AST Memory Registers Maps Values Events Globalenvs Smallstep Op Integers.
Require Import Smallstep Errors.
Require Import ListsExtra Before Permutation.
Require Import Graph GraphDual InfluenceRegion.
Require Import SharedTypes.
Require Import Lattice Ordered Kildall.
Require Import Coq.Program.Equality Wfsimpl.

Module NatIndexed.
  Definition t := nat.
  Definition index (n: nat): positive := Pos.of_succ_nat n.
  Lemma index_inj: forall (x y: nat), index x = index y -> x = y.
  Proof.
    unfold index. intros. extlia.
  Qed.
  Lemma eq: forall (x y: nat), {x = y} + {x <> y}.
  Proof.
    decide equality.
  Qed.
End NatIndexed.

Module OrderedNat := OrderedIndexed(NatIndexed).
(* Module PCSet := FSetAVL.Make(OrderedNat). *)
Module PCSet := FSetAVL.Make(OrderedPositive).


Module LRegset := LFSet(Regset).
Module LPCSet := LFSet(PCSet).
Module LTaint := LProd(LRegset)(LPCSet).

Module DS := Dataflow_Solver(LTaint)(NodeSetForward).

Lemma ge_antisym_reg: forall x y, LRegset.ge x y -> LRegset.ge y x -> LRegset.eq x y.
Proof.
  unfold LRegset.ge, LRegset.eq, Regset.Equal, Regset.Subset. split; intros. now apply H0 in H1. now apply H in H1.
Qed.

Lemma ge_antisym_pc: forall x y, LPCSet.ge x y -> LPCSet.ge y x -> LPCSet.eq x y.
Proof.
  unfold LPCSet.ge, LPCSet.eq, PCSet.Equal, PCSet.Subset. split; intros. now apply H0 in H1. now apply H in H1.
Qed.

Lemma ge_antisym_prod: forall x y, LTaint.ge x y -> LTaint.ge y x -> LTaint.eq x y.
Proof.
  unfold LTaint.eq, LTaint.ge. intros. destruct x; destruct y; intuition; simpl in *. apply ge_antisym_reg; auto. apply ge_antisym_pc; auto.
Qed.


(* Taint Analysis. *)

Section TaintAna.

(* What is required for a taint ana *)
Record taint_func: Type := {
  code: PTree.t instruction;
  taint_attr: fun_taint_attr reg;
  g: G;
  exit: nat;
  n: nat;
  idx: list nat;
  IDX: top_sort g idx;
  N: n > 0;
  VS: g.(vs) = seq 0 n;
  NCODE: forall pc, code @! pc <> None <-> pc < n;
  EXIT: forall v, v = exit <-> is_exit g v;
}.

Variable f: taint_func.

Definition ipd := ipd f.(g) f.(exit) f.(EXIT) f.(idx) f.(IDX).
Notation "x ∈ 'ir' ( c )" := (in_ir f.(g) f.(exit) f.(EXIT) f.(idx) f.(IDX) c x) (at level 50).
Notation "x ∈ 'ir_inn' ( c )" := (x ∈ ir(c) /\ x <> ipd c) (at level 50).

Definition in_ir_inner_dec := in_ir_inner_dec f.(g) f.(exit) f.(EXIT) f.(idx) f.(IDX).

(* Transfer function and initial state *)

Definition transf_regs (pc: positive) (t: LTaint.t) :=
  match f.(code) ! pc with
  | Some (Iop op src tgt) =>
    if Regset.exists_ (fun t => in_dec peq t src) (fst t) ||
       PCSet.exists_ (fun c => in_ir_inner_dec (Pos_to_pred_nat c) (Pos_to_pred_nat pc)) (snd t)
    then Regset.add tgt (fst t) else (fst t)
  | Some (Iload chunk addr args dst) =>
    if Regset.exists_ (fun t => in_dec peq t args) (fst t)
      (* Do not consider IRs: an Iload inside a tainted IR will be forbidden after the taint ana *)
    then Regset.add dst (fst t) else (fst t)
  | _ => fst t
  end.

Definition transf_conds (pc: positive) (t: LTaint.t) :=
  match f.(code) ! pc with
  | Some (Icond c regs) =>
    if Regset.exists_ (fun t => in_dec peq t regs) (fst t)
    then PCSet.add pc (snd t) else (snd t)
  | _ => snd t
  end.

Definition transf (pc: positive) (t: LTaint.t) :=
  (transf_regs pc t, transf_conds pc t).

Lemma transf_keeps_bottom: forall x, DS.L.eq (transf x DS.L.bot) DS.L.bot.
Proof.
  intros. unfold transf, transf_regs, transf_conds. simpl. split.
  case (f.(code) ! x) eqn:?; try case i eqn:?; apply LRegset.eq_refl.
  case (f.(code) ! x) eqn:?; try case i eqn:?; apply LPCSet.eq_refl.
Qed.

Lemma transf_monotone: forall pc t,
  LTaint.ge (transf pc t) t.
Proof.
  intros. unfold transf, transf_regs, transf_conds.
  split; simpl; case (f.(code) ! pc) eqn:?; try case i eqn:?; try case (_ || _);
  (try apply LRegset.ge_refl, LRegset.eq_refl);
  (try apply LPCSet.ge_refl, LPCSet.eq_refl).
  * unfold LRegset.ge, Regset.Subset. apply Regset.add_2.
  * unfold LRegset.ge, Regset.Subset. case (Regset.exists_). now apply Regset.add_2. auto.
  * unfold LPCSet.ge, PCSet.Subset. case (Regset.exists_). now apply PCSet.add_2. auto.
Qed.

Fixpoint set_from_list (l: list reg): Regset.t :=
  match l with
  | nil => Regset.empty
  | r::rs => Regset.add r (set_from_list rs)
  end.

Lemma set_from_list_spec: forall l r,
  Regset.mem r (set_from_list l) = true <-> In r l.
Proof.
  intros. induction l; split; intro.
  * simpl in H. pose Regset.empty_1. unfold Regset.Empty in e. apply Regset.mem_2 in H. now apply e in H.
  * easy.
  * simpl in H. case (peq r a) eqn:?. subst. apply in_eq.
    apply Regset.mem_2, Regset.add_3, Regset.mem_1 in H; [|lia]. apply IHl in H. now apply in_cons.
  * destruct H. subst. simpl. apply Regset.mem_1. now apply Regset.add_1.
    simpl. apply Regset.mem_1, Regset.add_2, Regset.mem_2. now apply IHl in H.
Qed.

Definition initial_taint: LTaint.t :=
  (set_from_list f.(taint_attr).(tainted_params), LPCSet.bot).

Lemma initial_taint_spec: forall r,
  Regset.mem r (fst initial_taint) = true <-> In r (f.(taint_attr).(tainted_params)).
Proof.
  apply set_from_list_spec.
Qed.

(*** DEFINITION OF SUCCESSORS TREE ***)

Definition pc_valid pc := Pos_to_pred_nat pc < f.(n).

Lemma pc_valid_vertex: forall v,
  vertex f.(g) v <->
  pc_valid (Pos.of_succ_nat v).
Proof.
  intros. unfold pc_valid, vertex. rewrite predsucc, VS, in_seq. lia.
Qed.

Definition all_starts: list V := filter (fun v => match predecessors f.(g) v with nil => true | _ => false end) f.(g).(vs).

Lemma all_starts_spec: forall s,
  In s all_starts <-> is_start f.(g) s.
Proof.
  intros. unfold all_starts, is_start. rewrite filter_In. unfold vertex. now case predecessors.
Qed.

Lemma all_starts_nonempty: exists s, In s all_starts.
Proof.
  exploit top_sort_first_start. apply f.(IDX). rewrite VS, seq_length. apply f.(N).
  intros. eexists (nth 0 (idx f) _). enow rewrite all_starts_spec.
  Unshelve. exact 0.
Qed.

(* A PTree that, instead of containing instructions, contains only the successors (as positive values).
   In addition, the successor of the exit node are all nodes without predecessors. *)
Definition succs: PTree.t (list positive) :=
  PTree.map
    (fun pc _ => map Pos.of_succ_nat (if Pos_to_pred_nat pc =? f.(exit) then all_starts else successors f.(g) (Pos_to_pred_nat pc)))
    f.(code).

Lemma succs_edge: forall v w s,
  v → w in f.(g) ->
  succs @! v = Some s ->
  In (Pos.of_succ_nat w) s.
Proof.
  intros. unfold succs in H0. rewrite PTree.gmap in H0. unfold Coqlib.option_map in H0. case (f.(code) @! v) in H0; [|congruence].
  injection H0. intro. rewrite <- H1. apply in_map.
  case (Nat.eq_dec v f.(exit)) eqn:?.
  * subst. exfalso. apply edge_exit in H; auto. now apply f.(EXIT).
  * case (_ =? _) eqn:?. rewrite predsucc, Nat.eqb_eq in Heqb. lia.
    rewrite predsucc. enow apply successors_spec.
Qed.

Lemma succs_exit: forall s st,
  is_start f.(g) s ->
  succs @! (exit f) = Some st ->
  In (Pos.of_succ_nat s) st.
Proof.
  intros. unfold succs in H0. rewrite PTree.gmap in H0. unfold Coqlib.option_map in H0. case (f.(code) @! (exit f)) in H0; [|congruence].
  injection H0. intro. rewrite <- H1. apply in_map.
  rewrite predsucc, Nat.eqb_refl. now apply all_starts_spec.
Qed.

Lemma succs_vertex_full: forall v,
  vertex f.(g) v ->
  exists i s, succs ! (Pos.of_succ_nat v) = Some i /\ In s i /\ pc_valid s.
Proof.
  intros.
  unfold succs. rewrite PTree.gmap. unfold Coqlib.option_map. case (f.(code) @! v) eqn:?.
  2: { exfalso. assert (v < n f). unfold vertex in H. rewrite VS, in_seq in H. lia. apply NCODE in H0. congruence. }
  rewrite predsucc. case (v =? f.(exit)) eqn:?.
  * rewrite Nat.eqb_eq in Heqb. destruct all_starts_nonempty.
    exists (map Pos.of_succ_nat all_starts), (Pos.of_succ_nat x). split; auto. split. now apply in_map.
    apply all_starts_spec in H0 as []. now apply pc_valid_vertex.
  * rewrite Nat.eqb_neq in Heqb. destruct (successors f.(g) v) eqn:?.
    exfalso. assert (is_exit f.(g) v) by easy. now apply EXIT in H0.
    exists (map Pos.of_succ_nat (v0::l)), (Pos.of_succ_nat v0). split; auto. split. apply in_map, in_eq.
    apply pc_valid_vertex. enough (v → v0 in f.(g)) by auto. apply successors_spec; auto. rewrite Heql. apply in_eq.
Qed.

Lemma succs_vertex: forall v,
  vertex f.(g) v ->
  exists i, succs ! (Pos.of_succ_nat v) = Some i.
Proof.
  intros. apply succs_vertex_full in H. decompose [ex and] H. now exists x.
Qed.


(*** ANALYSIS ***)

Definition res := DS.fixpoint succs id transf (Pos.of_succ_nat f.(exit)) initial_taint.

(* Assume that there is a result - instantiate this from outside. *)
Hypothesis result_valid: { result | res = Some result }.

Definition result := (!result_valid) @!! (exit f).

(* Definition of tainted regs and conds *)
Definition tainted_regs := fst result.
Definition tainted_reg r := Regset.mem r tainted_regs.
Definition tainted_cond v := PCSet.mem (Pos.of_succ_nat v) (snd result).
Definition uniform_cond v := negb (tainted_cond v).

(* Some (simple but wordy) proofs about the final taint result *)

Lemma edge_gt: forall res' v w,
  res = Some res' ->
  (v → w in f.(g) \/ (v = f.(exit) /\ is_start f.(g) w)) ->
  LTaint.ge (res' @!! w) (res' @!! v).
Proof.
  intros.
  assert (vertex f.(g) v). { destruct H0; auto. destruct H0. subst. now apply EXIT. }
  apply succs_vertex in H1 as [].
  eapply DS.fixpoint_solution in H. 2: exact H1.
  2: { destruct H0. enow apply succs_edge with (s:=x) in e.
       destruct a. subst. enow eapply succs_exit in H1. }
  2: apply transf_keeps_bottom.
  eapply LTaint.ge_trans. exact H. apply transf_monotone.
Qed.

Lemma path_gt: forall res' v w,
  res = Some res' ->
  v →* w in f.(g) ->
  LTaint.ge (res' @!! w) (res' @!! v).
Proof.
  intros.
  induction H0. apply LTaint.ge_refl, LTaint.eq_refl.
  apply LTaint.ge_trans with (y := res' @!! v); auto.
  assert (vertex f.(g) u) by auto. apply succs_vertex in H2 as [].
  eapply DS.fixpoint_solution in H. 2: exact H2. 2: enow apply succs_edge with (s:=x) in H0. 2: apply transf_keeps_bottom.
  eapply LTaint.ge_trans. exact H. apply transf_monotone.
Qed.

Lemma everywhere_equal: forall result' pc,
  res = Some result' ->
  pc_valid pc ->
  LTaint.eq (result' !! pc) result.
Proof.
  intros. unfold result. destruct result_valid. rewrite e in H. injection H. intro. subst. simpl.
  set (v := Pos_to_pred_nat pc). assert (pc = Pos.of_succ_nat v) by (unfold Pos_to_pred_nat, v; now rewrite succpred). rewrite H1.
  assert (v →* f.(exit) in f.(g)). {
    exploit top_sort_path_to_exit. Unshelve. 7: exact v. apply f.(IDX). rewrite VS, seq_length. apply N. apply pc_valid_vertex. now rewrite <- H1.
    intros [? []]. apply EXIT in H2. now subst x.
  }
  assert (exists s, is_start f.(g) s /\ s →* v in f.(g)) as [s []]. {
    exploit top_sort_path_from_start. Unshelve. 7: exact v. apply f.(IDX). apply pc_valid_vertex. now rewrite <- H1. rewrite VS, seq_length. apply N. auto.
  }
  assert (LTaint.ge (result' @!! (exit f)) (result' @!! v)) by enow eapply path_gt with (v:=v) (w:=f.(exit)) in e.
  assert (LTaint.ge (result' @!! s) (result' @!! (exit f))) by enow eapply edge_gt.
  assert (LTaint.ge (result' @!! v) (result' @!! s)) by enow eapply path_gt with (v:=s) (w:=v) in e; eauto.
  apply LTaint.ge_trans with (z := result' @!! (exit f)) in H7; eauto.
  now apply ge_antisym_prod.  
Qed.

Lemma everywhere_equal_transf: forall result' pc,
  res = Some result' ->
  pc_valid pc ->
  LTaint.eq result (transf pc (result' !! pc)).
Proof.
  intros. copy H.
  set (v := Pos_to_pred_nat pc). assert (vertex f.(g) v) by (apply pc_valid_vertex; unfold v; now rewrite succpred).
  apply succs_vertex_full in H2. decompose [ex and] H2.
  assert (LTaint.ge (result' !! x0) (transf pc (result' !! pc))). {
    eapply DS.fixpoint_solution; eauto. unfold v in H3. now rewrite succpred in H3. apply transf_keeps_bottom.
  }
  assert (LTaint.ge (transf pc (result' !! pc)) (result' !! pc)) by apply transf_monotone.
  copy H. eapply everywhere_equal with (pc:=x0) in H; eauto. eapply everywhere_equal with (pc:=pc) in H8; eauto.
  apply LTaint.eq_sym in H. apply LTaint.ge_refl in H, H8.
  apply ge_antisym_prod. now apply LTaint.ge_trans with (y:=result'!!x0). now apply LTaint.ge_trans with (y:=result'!!pc).
Qed.
  
Lemma regset_ge: forall r r1 r2,
  LRegset.ge r2 r1 -> Regset.mem r r1 = true -> Regset.mem r r2 = true.
Proof.
  intros. unfold LRegset.ge, Regset.Subset in H. apply Regset.mem_1, H, Regset.mem_2, H0.
Qed.

Lemma pcset_ge: forall r r1 r2,
  LPCSet.ge r2 r1 -> PCSet.mem r r1 = true -> PCSet.mem r r2 = true.
Proof.
  intros. unfold LPCSet.ge, Regset.Subset in H. apply PCSet.mem_1, H, PCSet.mem_2, H0.
Qed.

Lemma _helper1: forall src,
  SetoidList.compat_bool (fun x y : OrderedPositive.t => x = y) (fun t0 : Regset.elt => in_dec peq t0 src).
Proof.
  unfold SetoidList.compat_bool, Morphisms.Proper, Morphisms.respectful. intros. now subst.
Qed.

Lemma _helper2: forall v,
  SetoidList.compat_bool (fun x y : OrderedPositive.t => x = y)
    (fun c0 : PCSet.elt => in_ir_inner_dec (Pos_to_pred_nat c0) (Pos_to_pred_nat (Pos.of_succ_nat v))).
Proof.
  unfold SetoidList.compat_bool, Morphisms.Proper, Morphisms.respectful. intros. now subst.
Qed.

Lemma taint_ana_respects_reg_use_op: forall v op dst src r,
  f.(code) @! v = Some (Iop op src dst) ->
  In r src ->
  tainted_reg r = true ->
  tainted_reg dst = true.
Proof.
  intros.
  destruct result_valid as [res].
  set (pc := Pos.of_succ_nat v).
  assert (vertex f.(g) v). { unfold vertex. rewrite f.(VS), in_seq. enough (v < n f) by lia. apply f.(NCODE). congruence. }
  assert (Regset.In r (fst res @!! v)). {
    apply everywhere_equal; auto. now apply pc_valid_vertex. now apply Regset.mem_2.
  }
  set (t := transf pc (res !! pc)).
  assert (Regset.mem dst (fst t) = true). {
    unfold transf, transf_regs in t. unfold pc in t. case (f.(code) @! v) eqn:? in t; try case i eqn:? in t; try congruence.
    unfold t. simpl. assert (r0 = dst) by congruence. assert (l = src) by congruence. subst r0 src.
    enough (Regset.exists_ (fun t0 : Regset.elt => in_dec peq t0 l) (fst res @!! v) = true).
    * rewrite H4. simpl. now apply Regset.mem_1, Regset.add_1.
    * apply Regset.exists_1; auto. apply _helper1. exists r. split; auto. now destruct in_dec.
  }
  unfold tainted_reg, tainted_regs. unfold t in H4. apply everywhere_equal_transf with (pc:=pc) in e; auto.
  * eapply regset_ge; eauto. destruct e. now apply LRegset.ge_refl.
  * unfold pc_valid, pc. rewrite predsucc. apply f.(NCODE). congruence.
Qed.

Lemma taint_ana_respects_reg_use_load: forall v chunk addr args dst r,
  f.(code) @! v = Some (Iload chunk addr args dst) ->
  In r args ->
  tainted_reg r = true ->
  tainted_reg dst = true.
Proof.
  intros.
  destruct result_valid as [res].
  set (pc := Pos.of_succ_nat v).
  assert (vertex f.(g) v). { unfold vertex. rewrite f.(VS), in_seq. enough (v < n f) by lia. apply f.(NCODE). congruence. }
  assert (Regset.In r (fst res @!! v)). {
    apply everywhere_equal; auto. now apply pc_valid_vertex. now apply Regset.mem_2.
  }
  set (t := transf pc (res !! pc)).
  assert (Regset.mem dst (fst t) = true). {
    unfold transf, transf_regs in t. unfold pc in t. case (f.(code) @! v) eqn:? in t; try case i eqn:? in t; try congruence.
    unfold t. simpl. assert (r0 = dst) by congruence. assert (l = args) by congruence. subst r0 args.
    enough (Regset.exists_ (fun t0 : Regset.elt => in_dec peq t0 l) (fst res @!! v) = true).
    * rewrite H4. simpl. now apply Regset.mem_1, Regset.add_1.
    * apply Regset.exists_1; auto. apply _helper1. exists r. split; auto. now destruct in_dec.
  }
  unfold tainted_reg, tainted_regs. unfold t in H4. apply everywhere_equal_transf with (pc:=pc) in e; auto.
  * eapply regset_ge; eauto. destruct e. now apply LRegset.ge_refl.
  * unfold pc_valid, pc. rewrite predsucc. apply f.(NCODE). congruence.
Qed.

Lemma taint_ana_respects_ir: forall c v op src dst,
  f.(code) @! v = Some (Iop op src dst) ->
  tainted_cond c = true ->
  v ∈ ir_inn(c) ->
  tainted_reg dst = true.
Proof.
  intros.
  destruct result_valid as [res].
  set (pc := Pos.of_succ_nat v). set (c' := Pos.of_succ_nat c).
  assert (vertex f.(g) v). { unfold vertex. rewrite f.(VS), in_seq. enough (v < n f) by lia. apply f.(NCODE). congruence. }
  assert (PCSet.In c' (snd res @!! v)). {
    apply everywhere_equal; auto. now apply pc_valid_vertex. now apply PCSet.mem_2.
  }
  set (t := transf pc (res !! pc)).
  assert (Regset.mem dst (fst t) = true). {
    unfold transf, transf_regs in t. unfold pc in t. case (f.(code) @! v) eqn:? in t; try case i eqn:? in t; try congruence.
    unfold t. simpl. assert (r = dst) by congruence. assert (l = src) by congruence. subst r src.
    enough (PCSet.exists_ (fun c0 : PCSet.elt => in_ir_inner_dec (Pos_to_pred_nat c0) (Pos_to_pred_nat (Pos.of_succ_nat v))) (snd res @!! v) = true).
    * rewrite H4, orb_true_r. now apply Regset.mem_1, Regset.add_1.
    * apply PCSet.exists_1; auto. apply _helper2. exists c'. split; auto. unfold c'. do 2 rewrite predsucc. now destruct in_ir_inner_dec.
  }
  unfold tainted_reg, tainted_regs. unfold t in H4. apply everywhere_equal_transf with (pc:=pc) in e; auto.
  * eapply regset_ge; eauto. destruct e. now apply LRegset.ge_refl.
  * unfold pc_valid, pc. rewrite predsucc. apply f.(NCODE). congruence.
Qed.

Lemma tainted_cond_spec: forall v cond r regs,
  f.(code) @! v = Some (Icond cond regs) ->
  In r regs ->
  tainted_reg r = true ->
  tainted_cond v = true.
Proof.
  intros.
  destruct result_valid as [res].
  set (pc := Pos.of_succ_nat v).
  assert (vertex f.(g) v). { unfold vertex. rewrite f.(VS), in_seq. enough (v < n f) by lia. apply f.(NCODE). congruence. }
  assert (Regset.In r (fst res @!! v)). {
    apply everywhere_equal; auto. now apply pc_valid_vertex. now apply Regset.mem_2.
  }
  set (t := transf pc (res !! pc)).
  assert (PCSet.mem pc (snd t) = true). {
    unfold transf, transf_conds in t. unfold pc in t. case (f.(code) @! v) eqn:? in t; try case i eqn:? in t; try congruence.
    unfold t. simpl. assert (c = cond) by congruence. assert (l = regs) by congruence. subst c l.
    enough (Regset.exists_ (fun t0 : Regset.elt => in_dec peq t0 regs) (fst res @!! v) = true).
    * rewrite H4. now apply PCSet.mem_1, PCSet.add_1.
    * apply Regset.exists_1; auto. apply _helper1. exists r. split; auto. now destruct in_dec.
  }
  unfold tainted_cond. unfold t in H4. apply everywhere_equal_transf with (pc:=pc) in e; auto.
  * eapply pcset_ge; eauto. destruct e. now apply LPCSet.ge_refl.
  * unfold pc_valid, pc. rewrite predsucc. apply f.(NCODE). congruence.
Qed.

Lemma taint_ana_params_spec: forall r,
  In r f.(taint_attr).(tainted_params) ->
  tainted_reg r = true.
Proof.
  intros.
  destruct result_valid as [res]. copy e. apply DS.fixpoint_entry in e.
  unfold tainted_reg, tainted_regs. eapply everywhere_equal with (pc := Pos.of_succ_nat (exit f)) in e0 as [].
  destruct e. apply Regset.mem_1, H0, H2, Regset.mem_2. now apply set_from_list_spec.
  now apply pc_valid_vertex, f.(EXIT).
Qed.

(* Now we have defined a set of tainted regs and from there a set of tainted conditions.
   We will now define uni(v) which states whether the predicate of a pc is uniform.
   We define it via influence regions, but it is equivalent to the uni-definition in the PCFL paper. *)

Definition uni pc := forall c, tainted_cond c = true -> ~ pc ∈ ir_inn(c).

Lemma uni_rev: forall pc, uni pc -> forall c, pc ∈ ir_inn(c) -> tainted_cond c = false.
Proof.
  intros. case tainted_cond eqn:?; auto. exfalso. now apply H in H0.
Qed.

Lemma ir_inn_n: forall c v,
  c >= f.(n) -> ~ v ∈ ir_inn(c).
Proof.
  intros. intros []. apply in_ir_vertex in H0 as [].
  unfold vertex in H0. rewrite f.(VS), in_seq in H0. lia.
Qed.

Lemma uni_equiv: forall pc, uni pc <-> (forall c, c < f.(n) -> tainted_cond c = false \/ ~ pc ∈ ir_inn(c)).
Proof.
  intros. unfold uni. split; intros.
  * case tainted_cond eqn:?; auto.
  * intro. case (lt_dec c f.(n)) eqn:?. clear Heqs. apply H in l as []; congruence. eapply ir_inn_n. 2: exact H1. lia.
Qed.

Definition uni_dec pc: {uni pc} + {~ uni pc}.
Proof.
  destruct (forallb (fun c => negb (tainted_cond c) || negb (in_ir_inner_dec c pc)) (seq 0 f.(n))) eqn:?.
  * left. apply uni_equiv. intros. rewrite forallb_forall in Heqb.
    assert (In c (seq 0 f.(n))) by (apply in_seq; lia). apply Heqb in H0.
    apply orb_true_iff in H0 as [].
    + left. now rewrite negb_true_iff in H0.
    + right. now destruct in_ir_inner_dec.
  * right. intro. rewrite uni_equiv in H. eassert (~ forallb _ _ = true) by (intro; now rewrite H0 in Heqb).
    apply H0. apply forallb_forall. intros. assert (x < f.(n)) by (rewrite in_seq in H1; lia).
    apply orb_true_iff. apply H in H2 as [].
    + left. now rewrite H2.
    + right. now destruct in_ir_inner_dec.
Qed.

(* Prove that our definition of uni coincides with the one of Hack-Moll. *)

Section UniPCFL.

Notation "v ▷ w" := (postdom f.(g) f.(exit) w v) (at level 50).

Definition is_cdep v '(a,b) := (a → b in f.(g) /\ b ▷ v /\ ~ a ▷ v).

Lemma cdep_vert: forall v a b, is_cdep v (a,b) -> v <> a /\ a →* v in f.(g).
Proof.
  intros. destruct H, H0. split. intro. subst. apply H1, postdom_refl. now apply f. auto.
  eapply postdom_path in H0. auto. apply f. rewrite VS, seq_length. apply N. apply f.
Qed.

Lemma vert: forall v, vertex f.(g) v -> In v f.(idx).
Proof.
  intros. eapply idx_in; eauto. apply f.
Qed.

Definition meas v := if vertex_dec f.(g) v then !(index_nat f.(idx) v ltac:(now apply vert)) else f.(n).

Program Definition uni_cdep_rec (v: nat) (uni: forall w, meas w < meas v -> Prop): Prop :=
  forall c w (cdep: is_cdep v (c,w)), uni c _ /\ uniform_cond c = true.
Next Obligation.
  pose proof top_sort_nodup f.(g) f.(idx) f.(IDX). pose proof f.(IDX).
  unfold meas. case vertex_dec eqn:?; [|now destruct H]. case vertex_dec eqn:? in |- *; [| now destruct H0].
  repeat destruct index_nat. simpl.
  enough (c << v in f.(idx)) by enow eapply _before_unfold_lt; eauto.
  apply beforeeq_trans_2 with (y:=w); eauto. enow eapply edge_before. eapply postdom_beforeeq; eauto. split; intro; now apply f.
Qed.

Definition uni_cdep := Fixm meas uni_cdep_rec.

Lemma uni_cdep_spec: forall v (V: vertex f.(g) v),
  uni_cdep v <-> forall c w, is_cdep v (c,w) -> uni_cdep c /\ uniform_cond c = true.
Proof.
  intro. 
  split; intros.
  * unfold uni_cdep in H. rewrite unroll_Fixm in H.
    unfold uni_cdep_rec in H at 1. intros. now apply H in H0.
  * unfold uni_cdep. rewrite unroll_Fixm. unfold uni_cdep_rec at 1.
    intros. now apply H in cdep.
Qed.

Lemma cdep_ir_relation: forall v c w,
  is_cdep v (c,w) -> v ∈ ir_inn(c).
Proof.
  pose proof top_sort_nodup f.(g) f.(idx) f.(IDX) as ND. pose proof f.(IDX) as I.
  unfold is_cdep. intros. destruct H, H0.
  assert (E: c <> exit f). { intro. apply EXIT in H2 as []. apply successors_spec in H; auto. now rewrite H3 in H. }
  split. apply in_ir_spec.
  * intro. apply EXIT in H2 as []. apply successors_spec in H; auto. now rewrite H3 in H.
  * split; [|split].
  + eapply postdom_path in H0; eauto. rewrite VS, seq_length. apply N. split; intro; now apply f.
  + intro. subst. apply H1, postdom_refl. now apply f. auto.
  + assert (w ∈ ir(c)) by now apply ir_edge_head. apply ir_pd in H2.
    eapply postdom_linear_dec in H2. 4: apply H0. 2: split; intro; now apply f. 2: apply I.
    destruct H2; auto. exfalso. apply H1. eapply postdom_concat. apply p.
    enow apply ir_pd_head.
  * intro. subst. enow apply H1, ir_pd_head.
Qed.

Definition postdom_dec := postdom_dec f.(g) f.(exit) f.(EXIT) f.(idx) f.(IDX).
Definition PD c v := filter (fun x => in_ir_inner_dec c x && postdom_dec x v) f.(g).(vs).

Lemma PD_spec: forall x c v, In x (PD c v) <-> x ∈ ir_inn(c) /\ x ▷ v.
Proof.
  split; intros.
  * apply filter_In in H as []. apply andb_prop in H0 as [].
    split. now destruct in_ir_inner_dec. now destruct postdom_dec.
  * destruct H. apply filter_In. split. now destruct H0. apply andb_true_iff.
    split. now destruct in_ir_inner_dec. now destruct postdom_dec.
Qed.

Lemma list_has_idx_min: forall (l: list V), l <> nil -> incl l f.(idx) ->
  exists min, In min l /\ forall elem, In elem l -> min <<= elem in f.(idx).
Proof.
  intros. induction l. congruence.
  case l in *.
  * exists a. split. apply in_eq. intros. destruct H1; [|easy]. subst. apply (beforeeq_id Nat.eq_dec). apply H0, in_eq.
  * assert (v :: l <> nil) by easy. apply IHl in H1 as [min []].
    2: { intro. intro. destruct H2. rewrite <- H2. apply H0, in_cons, in_eq. apply H0, in_cons, in_cons, H2. }
    case (beforeeq_dec Nat.eq_dec f.(idx) min a) as []. apply H0, in_cons, H1. apply H0, in_eq.
    + exists min. split. apply in_cons, H1. intros. destruct H3. subst. now apply before_yields_eq. now apply H2.
    + exists a. split. apply in_eq. intros. destruct H3.
      subst. apply (beforeeq_id Nat.eq_dec). apply H0, in_eq.
      apply beforeeq_trans with (y:=min). eapply top_sort_nodup. apply f. auto. now apply H2.
Qed.

Lemma PD_min: forall c v, v ∈ ir_inn(c) ->
  exists x, In x (PD c v) /\ forall x', In x' (PD c v) -> x <<= x' in f.(idx).
Proof.
  intros.
  assert (In v (PD c v)). { apply PD_spec. split; auto. apply postdom_refl. now apply f. destruct H. now apply in_ir_vertex in H. }
  assert (PD c v <> nil) by (intro; now rewrite H1 in H0). apply list_has_idx_min in H1 as [min []]. now exists min.
  intro. intro. apply PD_spec in H2 as []. destruct H3, H4. eapply idx_in; eauto. apply f.
Qed.

Lemma ir_cdep_relation: forall c v,
  v ∈ ir_inn(c) -> exists c' w, (c' ∈ ir_inn(c) \/ c' = c) /\ is_cdep v (c',w).
Proof.
  intros. copy H. apply PD_min in H0 as [w []]. apply PD_spec in H0 as [].
  destruct H0. apply ir_predecessor in H0 as [c' [? []]].
  assert (~ c' ▷ v).
  + destruct H0. intro. assert (In c' (PD c v)) by now apply PD_spec. apply H1 in H7.
    eapply edge_before in H5. 2: apply f. apply (beforeeq_swap Nat.eq_dec) in H7. auto. eapply top_sort_nodup, f.
    subst. intro. eapply pd_outside_ir in H0. now apply H0 in H. destruct H. apply in_ir_spec in H. lia. now apply in_ir_vertex in H.
  + exists c', w. split. destruct H0. now left. now right. now split. 
Qed.

Lemma ir_absorb_ipd: forall c v,
  v ∈ ir_inn(c) ->
  ipd v ▷ ipd c.
Proof.
  intros.
  case (Nat.eq_dec (ipd v) (ipd c)). { intros. rewrite e. apply postdom_refl. now apply f. apply ipd_vertex. destruct H. now apply in_ir_vertex in H. destruct H. now apply in_ir_vertex in H. }
  intro H0. destruct H. copy H. apply ir_pd in H. assert (vertex f.(g) v) by now destruct H.
  assert (vertex f.(g) c) by now apply in_ir_vertex in H2. eapply ipd_is_ipd in H3.
  Unshelve. 2: { intro. apply H1. rewrite H5 in *. now apply ir_exit_ipd. } 2: apply f. 3: apply f.
  destruct H3, H5. apply H6 in H; auto.
  assert (vertex f.(g) v) by now destruct H3. eapply ir_pd_head in H4.
  Unshelve. 4: apply f. 2: now apply in_ir_vertex in H2.
  apply ir_pd in H2. eapply postdom_linear_dec in H2. 2: split; intros; apply f. 2: auto. 2: auto. 2: apply f. 2: apply H3.
  destruct H2; eauto. exfalso. apply H0. eapply postdom_path in p. 2: apply f. 2: rewrite VS, seq_length; apply f. 2: split; auto; now apply f.
  eapply (beforeeq_both Nat.eq_dec); eauto. eapply top_sort_nodup. apply f.
  eapply path_beforeeq; eauto. split; intros; now apply f.
  eapply path_beforeeq; eauto. split; intros; now apply f.
  Unshelve. 4: apply f.
Qed.

Lemma ir_absorb: forall c v x,
  v ∈ ir_inn(c) ->
  x ∈ ir_inn(v)->
  x ∈ ir_inn(c).
Proof.
  intros. pose proof f.(IDX) as I.
  assert (V: vertex f.(g) v) by (destruct H; now apply in_ir_vertex in H). assert (C: vertex f.(g) c) by (destruct H; now apply in_ir_vertex in H).
  assert (EV: v <> exit f) by (destruct H0; now apply in_ir_vertex in H0). assert (EC: c <> exit f) by (destruct H; now apply in_ir_vertex in H).
  copy H. destruct H, H0. split.
  * apply in_ir_spec. now apply in_ir_vertex in H. apply ir_absorb_ipd in H1.
    apply in_ir_spec in H as [], H0 as []; auto. split; auto. split.
    intro. subst. eapply path_beforeeq in H, H0; eauto. destruct H4. apply H4. eapply (beforeeq_both Nat.eq_dec); eauto. enow eapply top_sort_nodup.
    eapply postdom_concat. apply H1. apply H5.
  * intro. subst. apply ir_absorb_ipd in H1. apply ir_pd in H0. apply H3.
    eapply (beforeeq_both Nat.eq_dec); eauto. enow eapply top_sort_nodup.
    eapply postdom_beforeeq; eauto. split; intros; now apply f.
    eapply postdom_beforeeq; eauto. split; intros; now apply f.
Qed.

Lemma uni_transfer: forall c v, uni v -> v ∈ ir_inn(c) -> uni c.
Proof.
  intros. unfold uni in *. intros. intro. apply H in H1. apply H1. enow eapply ir_absorb.
Qed.

Theorem uni_cdep_equivalent: forall v, vertex f.(g) v ->
  uni v <-> uni_cdep v.
Proof.
  pose (P x := uni x <-> uni_cdep x).
  intros. exploit strong_graph_ind. Unshelve. exact f.(IDX). 2: exact H. 3: exact P.
  unfold P. split; intros; clear v H; rename v0 into v.
  * apply uni_cdep_spec; auto. intros. copy H.
    apply cdep_ir_relation in H. copy H. apply uni_rev in H; auto. unfold uniform_cond. rewrite H. split; auto.
    apply cdep_vert in H3 as []. apply H1; auto. enow eapply uni_transfer.
  * intro. intro. intro. copy H3. apply ir_cdep_relation in H3 as [c' [w []]].
    rewrite uni_cdep_spec in H2; auto. copy H5. apply H2 in H5 as [].
    destruct H3.
    + apply H1 in H5. eapply H5. apply H. auto.
      destruct H6, H9. intro. apply H10. subst. apply postdom_refl. now apply f. auto.
      destruct H6, H9. eapply postdom_path in H9; eauto. apply f. rewrite VS, seq_length. now apply f. now apply f.
    + subst. unfold uniform_cond in H7. now rewrite H in H7.
  * now unfold P.
Qed.

End UniPCFL.

End TaintAna.