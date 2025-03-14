Require Import Axioms Common Coqlib Classical Datatypes.
Require Import AST Memory Registers Maps Values Events Globalenvs Smallstep Op Integers Floats.
Require Import ListsExtra Graph GraphDual TaintAnalysis SelRTL PredRTL SharedTypes.
Require Import Before.
Require Import PCFL PCFLBranchMapping PCFLEdgeEmbedding.
Require Import Smallstep Errors Linking.

Section Translation.

Variable f: PredRTL.function.

Definition uni := uni f.(taint_f) f.(TAINT_RES).
Definition uni_dec := uni_dec f.(taint_f) f.(TAINT_RES).

(*** New registers ***)

Definition maxreg := max_reg_function f.(PredRTL.code) f.(params).
Definition newmaxreg := (2 * maxreg)%positive.
Definition v_reg := Pos.succ newmaxreg.
Definition targ_reg := Pos.succ v_reg.
Definition targ_new_reg := Pos.succ targ_reg.
Definition livereg := Pos.succ targ_new_reg.
Definition cond_which_reg := Pos.succ livereg.

Definition dummy_reg (reg: reg) := (maxreg + reg)%positive.

Definition num_regs := Pos.to_nat maxreg.

Definition const_reg v := ((Pos.of_succ_nat v) + cond_which_reg)%positive.

Lemma num_regs_nonzero: num_regs > 0.
Proof.
  intros. unfold num_regs. lia.
Qed.

(*** Code transformation ***)

Definition nat2int val := Int.repr (Z.of_nat val).
Definition nat2val val := Vint (nat2int val).

Lemma nat2int_eq: forall a b,
  a < Z.to_nat (Int.modulus) ->
  b < Z.to_nat (Int.modulus) -> 
  nat2int a = nat2int b -> a = b.
Proof.
  Local Transparent Int.repr.
  intros. injection H1; intro.
  repeat rewrite Int.Z_mod_modulus_eq in H2.
  do 2 rewrite Z.mod_small in H2; lia.
Qed.

Lemma nat2val_eq: forall a b,
  a < Z.to_nat (Int.modulus) ->
  b < Z.to_nat (Int.modulus) -> 
  nat2val a = nat2val b -> a = b.
Proof.
  intros. apply nat2int_eq; auto. unfold nat2val in H1. congruence.
Qed.

Lemma nat2int_int_neq: forall a b,
  a < Z.to_nat (Int.modulus) ->
  b < Z.to_nat (Int.modulus) -> 
  a <> b ->
  Int.eq (nat2int a) (nat2int b) = false.
Proof.
  intros. case Int.eq eqn:?; auto.
  pose proof Int.eq_spec (nat2int a) (nat2int b). rewrite Heqb0 in H2. now apply nat2int_eq in H2.
Qed.

Lemma nat2int_int_eq: forall a,
  a < Z.to_nat (Int.modulus) -> 
  Int.eq (nat2int a) (nat2int a) = true.
Proof.
  intros. case Int.eq eqn:?; auto.
  pose proof Int.eq_spec (nat2int a) (nat2int a). now rewrite Heqb in H0.
Qed.

Fixpoint set_regs_seq rs n start : RTL.regset :=
  match n with 
  | 0 => rs
  | S n' => (set_regs_seq rs n' start) # (Pos.of_succ_nat (start + n')) <- (nat2val n')
  end.

Lemma set_regs_seq_new: forall rs n m start,
  m < n ->
  (set_regs_seq rs n start) # (Pos.of_succ_nat (start + m)) = nat2val m.
Proof.
  intros. induction n. lia.
  simpl. case (Nat.eq_dec m n) eqn:?.
  * now rewrite e, Regmap.gss.
  * rewrite Regmap.gso, IHn; auto; lia.
Qed.

Lemma set_regs_seq_old: forall rs n m start,
  m < start \/ m >= start + n ->
  (set_regs_seq rs n start) # (Pos.of_succ_nat m) = rs # (Pos.of_succ_nat m).
Proof.
  intros. induction n. auto.
  simpl. rewrite Regmap.gso, IHn; auto; extlia.
Qed.

Lemma set_regs_seq_lessdef_1: forall rs n start max,
  start > (Pos_to_pred_nat max) ->
  def_regset max rs ->
  regs_lessdef rs (set_regs_seq rs n start).
Proof.
  intros. intro. pose (r' := Pos_to_pred_nat r). replace r with (Pos.of_succ_nat r') by apply succpred.
  case (lt_dec r' start) eqn:?.
    enow rewrite set_regs_seq_old.
  case (ge_dec r' (start + n)) eqn:?.
    enow rewrite set_regs_seq_old.
  enough (U: rs !! (Pos.of_succ_nat r') = Vundef) by now rewrite U.
    eassert (~ (rs !! (Pos.of_succ_nat r')) <> Vundef).
    intro. apply H0 in H1. unfold r', Pos_to_pred_nat in *. extlia.
    case (_ !! _) eqn:?; try congruence; exfalso; apply H1; congruence. 
Qed.

Lemma set_regs_seq_lessdef_2: forall rs n start,
  (forall m, m < n -> rs # (Pos.of_succ_nat (start + m)) = Vundef) ->
  regs_lessdef rs (set_regs_seq rs n start).
Proof.
  intros. induction n. apply regs_lessdef_refl.
  simpl. apply lessdef_new_one.
  * apply IHn. intros. rewrite H. auto. lia.
  * apply H. lia.
Qed.

Lemma set_regs_seq_wt: forall rs n start env,
  (forall r, start <= r < start + n -> env (Pos.of_succ_nat r) = Tint) ->
  wt_regset env rs ->
  wt_regset env (set_regs_seq rs n start).
Proof.
  intros. induction n. auto.
  simpl. apply wt_regset_assign.
  * apply IHn. intros. apply H. lia.
  * rewrite H. constructor. lia.
Qed.


Definition set_v_instr (v: nat) := Iop (Ointconst (nat2int v)) nil v_reg.

Definition set_v_targ_new_instr (v: nat) :=
  match (successors f.(g_pred) v) with
  | s :: nil => Iop (Ointconst (nat2int s)) nil targ_new_reg
  | s1 :: s2 :: nil => Isel Tint cond_which_reg (const_reg s1) (const_reg s2) targ_new_reg
  | _ => Inop
  end.

Definition set_v_targ_instr :=
  (* TODO: could replace the Isel with Omov if uni: if andb (uni_dec v) (uniform_cond f v) then Iop Omove targ_reg (targ_new_reg::nil) else *)
  Isel Tint livereg targ_new_reg targ_reg targ_reg.

Definition set_live_instr := 
 (* TODO: could replace the Ocmp with Ointconst if uni: if (uni_dec v) then Iop (Ointconst (nat2int 1)) nil livereg else *)
 Iop (Ocmp (Ccomp Ceq)) (v_reg::targ_reg::nil) livereg.

Definition exec_instr_1 (v: nat) (i: option instruction) :=
  match i with
    | Some (Iop op args dst) => if uni_dec v then Iop op args dst else Iop op args (dummy_reg dst)
    | Some (Iload chunk addr args dst) => Iload chunk addr args dst
    | Some (Icond c args) => Iop (Ocmp c) args cond_which_reg
    | _ => Inop
end.

Definition exec_instr_2 (v: nat) (i: option instruction) := match i with
  | Some (Iop op args dst) => if uni_dec v then Inop else Isel (f.(env) dst) livereg (dummy_reg dst) dst dst
  | _ => Inop
end.

Definition closing_instr (v: nat) (i: option instruction) := match i with
  | Some (Icond c args) =>
    if (f.(uniform_cond) v) then
      Icond (Cmasknotzero (Int.one)) (cond_which_reg::nil)
    else Inop
  | Some (Ireturn r) => Ireturn r
  | _ => Inop
end.

Definition init_reg (e: regenv) (r: nat) := (* reg in 0..<num_regs, i.e. one less than the positive reg *)
  if (in_dec peq (Pos.of_succ_nat r) f.(params)) then
    Inop
  else match (e (Pos.of_succ_nat r)) with
    | Tint => Iop (Ointconst Int.zero) nil (Pos.of_succ_nat r)
    | Tfloat => Iop (Ofloatconst Float.zero) nil (Pos.of_succ_nat r)
    | Tlong => Iop (Olongconst Int64.zero) nil (Pos.of_succ_nat r)
    | Tsingle => Iop (Osingleconst Float32.zero) nil (Pos.of_succ_nat r)
    | Tany32 => Iop (Ointconst Int.zero) nil (Pos.of_succ_nat r)
    | Tany64 => Iop (Olongconst Int64.zero) nil (Pos.of_succ_nat r)
  end.

Definition set_int_reg (v: nat) (r: Pos.t) :=
  Iop (Ointconst (nat2int v)) nil r.

Definition elements := map (fun pc => (pc, f.(code) @! pc)) (seq 0 f.(n)).

Definition set_v_instrs := map (fun '(pc,i) => set_v_instr pc) elements.
Definition live_instrs := map (fun '(pc,i) => set_live_instr) elements.
Definition exec_instrs_1 := map (fun '(pc,i) => exec_instr_1 pc i) elements.
Definition exec_instrs_2 := map (fun '(pc,i) => exec_instr_2 pc i) elements.
Definition set_v_targ_new_instrs := map (fun '(pc,i) => set_v_targ_new_instr pc) elements.
Definition set_v_targ_instrs := map (fun '(pc,i) => set_v_targ_instr) elements.
Definition closing_instrs := map (fun '(pc,i) => closing_instr pc i) elements.


Lemma elements_length: length elements = f.(n).
Proof.
  unfold elements. now rewrite map_length, seq_length.
Qed.

Definition set_v_pc (pc: nat) := pc.
Definition live_pc pc := 1 * f.(n) + pc.
Definition instr_1_pc pc := 2 * f.(n) + pc.
Definition instr_2_pc pc := 3 * f.(n) + pc.
Definition set_v_targ_new_pc pc := 4 * f.(n) + pc.
Definition set_v_targ_pc pc := 5 * f.(n) + pc.
Definition closing_pc pc := 6 * f.(n) + pc.

Definition new_entry := 7 * f.(n).
Definition init_reg_pc reg := new_entry + reg. (* reg in 0..<num_regs, i.e. one less than the positive reg *)
Definition init_targ_new_pc := 7 * f.(n) + num_regs.
Definition init_targ_pc := S init_targ_new_pc.
Definition const_reg_pc v := S init_targ_pc + v.
Definition new_N := S init_targ_pc + f.(n). (* = 8 * f.(n) + num_regs + 2 *)

Definition init_reg_instrs_1 := map (init_reg f.(env)) (seq 0 num_regs).
Definition init_reg_instrs_2 := set_int_reg 0 targ_new_reg :: set_int_reg f.(PredRTL.entry) targ_reg :: nil.
Definition init_reg_instrs_3 := map (fun i => set_int_reg i (const_reg i)) (seq 0 f.(n)).


Ltac unfold_instrs := unfold set_v_instrs, live_instrs, exec_instrs_1, exec_instrs_2, set_v_targ_new_instrs, set_v_targ_instrs, closing_instrs, init_reg_instrs_1, init_reg_instrs_2, init_reg_instrs_3.
Ltac unfold_all_instrs := unfold set_v_instrs, live_instrs, exec_instrs_1, exec_instrs_2, set_v_targ_new_instrs, set_v_targ_instrs, closing_instrs, init_reg_instrs_1, init_reg_instrs_2, init_reg_instrs_3 in *.

Ltac unfold_pcs := unfold set_v_pc, live_pc, instr_1_pc, instr_2_pc, set_v_targ_new_pc, set_v_targ_pc, closing_pc,
                    new_N, const_reg_pc, init_targ_pc, init_targ_new_pc, init_reg_pc, new_entry.
Ltac unfold_all_pcs := unfold set_v_pc, live_pc, instr_1_pc, instr_2_pc, set_v_targ_new_pc, set_v_targ_pc, closing_pc,
                    new_N, const_reg_pc, init_targ_pc, init_targ_new_pc, init_reg_pc, new_entry in *.
Lemma instrs_lengths:
  length set_v_instrs = f.(n) /\
  length live_instrs = f.(n) /\
  length exec_instrs_1 = f.(n) /\
  length exec_instrs_2 = f.(n) /\
  length set_v_targ_new_instrs = f.(n) /\
  length set_v_targ_instrs = f.(n) /\
  length closing_instrs = f.(n) /\
  length init_reg_instrs_1 = num_regs /\
  length init_reg_instrs_2 = 2 /\
  length init_reg_instrs_3 = f.(n).
Proof.
  repeat split; unfold_instrs; [ | | | | | | |
    unfold init_reg_instrs_1; now rewrite map_length, seq_length | ];
    (try now rewrite map_length, elements_length);
    now rewrite map_length, seq_length.
Qed.

Definition transl_code: PTree.t instruction :=
  to_tree (set_v_instrs ++ live_instrs ++ exec_instrs_1 ++ exec_instrs_2 ++ set_v_targ_new_instrs ++ set_v_targ_instrs ++ closing_instrs ++ init_reg_instrs_1 ++ init_reg_instrs_2 ++ init_reg_instrs_3).


Lemma new_code_spec_1: forall pc,
  pc < f.(n) ->
  transl_code @! (set_v_pc pc) = Some (set_v_instr pc) /\
  transl_code @! (live_pc pc) = Some set_live_instr /\
  transl_code @! (instr_1_pc pc) = Some (exec_instr_1 pc (f.(code) @! pc)) /\
  transl_code @! (instr_2_pc pc) = Some (exec_instr_2 pc (f.(code) @! pc)) /\
  transl_code @! (set_v_targ_new_pc pc) = Some (set_v_targ_new_instr pc) /\
  transl_code @! (set_v_targ_pc pc) = Some set_v_targ_instr /\
  transl_code @! (closing_pc pc) = Some (closing_instr pc (f.(code) @! pc)).
Proof.
  intros. unfold transl_code, live_pc.
  pose proof instrs_lengths. pose proof elements_length.
  unfold_all_pcs. unfold_all_instrs. repeat rewrite to_tree_spec.
  repeat split.
  7: rewrite nth_error_app2; [|lia].
  6-7: rewrite nth_error_app2; [|lia].
  5-7: rewrite nth_error_app2; [|lia].
  4-7: rewrite nth_error_app2; [|lia].
  3-7: rewrite nth_error_app2; [|lia].
  2-7: rewrite nth_error_app2; [|lia].
  1-7: rewrite nth_error_app1; [|lia].
  Ltac solve pc :=
    erewrite map_nth_error with (d:=(pc,_)); auto;
    unfold elements; try erewrite map_nth_error; eauto;
    repeat rewrite map_length; try rewrite seq_length;
    erewrite <- nth_or_error; [|rewrite seq_length; lia]; f_equal; rewrite seq_nth; lia.
  all: solve pc.
  Unshelve.
  all: auto.
Qed.

Lemma new_code_spec_2: forall reg,
  reg < num_regs ->
  transl_code @! (init_reg_pc reg) = Some (init_reg f.(env) reg).
Proof.
  intros. unfold transl_code, live_pc.
  pose proof instrs_lengths. pose proof elements_length.
  unfold_all_pcs. unfold_all_instrs. repeat rewrite to_tree_spec.
  do 7 (rewrite nth_error_app2; try lia).
  rewrite nth_error_app1; try lia.
  repeat rewrite map_length.
  erewrite map_nth_error. eauto. erewrite <- nth_or_error; [|rewrite seq_length; lia]. f_equal. rewrite seq_nth; lia.
  Unshelve. auto.
Qed.

Lemma new_code_spec_3:
  transl_code @! init_targ_new_pc = Some (set_int_reg 0 targ_new_reg).
Proof.
  unfold transl_code.
  pose proof instrs_lengths. pose proof elements_length.
  unfold_all_pcs. unfold_all_instrs. rewrite to_tree_spec.
  do 8 (rewrite nth_error_app2; try lia).
  rewrite nth_error_app1; try lia.
  repeat rewrite map_length.
  rewrite seq_length, H0.
  eenough (_ - _ = 0) by now rewrite H1. lia.
Qed.

Lemma new_code_spec_4:
  transl_code @! init_targ_pc = Some (set_int_reg f.(PredRTL.entry) targ_reg).
Proof.
  unfold transl_code.
  pose proof instrs_lengths. pose proof elements_length.
  unfold_all_pcs. unfold_all_instrs. rewrite to_tree_spec.
  do 8 (rewrite nth_error_app2; try lia).
  rewrite nth_error_app1; try lia.
  repeat rewrite map_length.
  rewrite seq_length, H0.
  eenough (_ - _ = 1) by now rewrite H1. lia.
Qed.

Lemma new_code_spec_5: forall v,
  v < f.(n) ->
  transl_code @! (const_reg_pc v) = Some (set_int_reg v (const_reg v)).
Proof.
  intros. unfold transl_code.
  pose proof instrs_lengths. pose proof elements_length.
  unfold_all_pcs. unfold_all_instrs. rewrite to_tree_spec.
  do 9 (rewrite nth_error_app2; try lia).
  repeat rewrite map_length.
  rewrite H1.
  erewrite map_nth_error. eauto. erewrite <- nth_or_error; [|rewrite 2 seq_length; lia].
  f_equal. rewrite seq_nth. rewrite seq_length. pose proof f.(N). case f.(n). lia. intros. case n. lia. intros. lia.
  rewrite seq_length. lia.
  Unshelve. auto.
Qed.


(*** Graph transformation ***)

Definition set_v_edges := map (fun pc => (set_v_pc pc, live_pc pc)) f.(g).(vs).
Definition live_edges := map (fun pc => (live_pc pc, instr_1_pc pc)) f.(g).(vs).
Definition instr_1_edges := map (fun pc => (instr_1_pc pc, instr_2_pc pc)) f.(g).(vs).
Definition instr_2_edges := map (fun pc => (instr_2_pc pc, set_v_targ_new_pc pc)) f.(g).(vs).
Definition set_v_targ_new_edges := map (fun pc => (set_v_targ_new_pc pc, set_v_targ_pc pc)) f.(g).(vs).
Definition set_v_targ_edges := map (fun pc => (set_v_targ_pc pc, closing_pc pc)) f.(g).(vs).

Definition out_edges_for_v (pc: nat) := map (fun s => (closing_pc pc, s)) (successors f.(g) pc).
Definition closing_edges := flat_map (out_edges_for_v) f.(g).(vs).

Definition edges_for_vs :=
  set_v_edges ++ live_edges ++ instr_1_edges ++ instr_2_edges ++ set_v_targ_new_edges ++ set_v_targ_edges ++ closing_edges.

Definition edges_for_regs :=
  (new_N - 1, f.(entry)) ::
  map (fun s => (new_entry + s, new_entry + S s)) (seq 0 (num_regs+f.(n)+1)).

Ltac unfold_edges := unfold edges_for_vs, edges_for_regs, set_v_edges, live_edges, instr_1_edges, instr_2_edges, set_v_targ_new_edges, set_v_targ_edges, closing_edges, out_edges_for_v.
Ltac unfold_all_edges := unfold edges_for_vs, edges_for_regs, set_v_edges, live_edges, instr_1_edges, instr_2_edges, set_v_targ_new_edges, set_v_targ_edges, closing_edges, out_edges_for_v in *.

Definition transl_graph: G :=
  mkG (seq 0 new_N) ltac:(apply seq_NoDup) (edges_for_vs ++ edges_for_regs).


Lemma transl_vertex: forall v,
  v < new_N -> vertex transl_graph v.
Proof.
  intros. unfold transl_graph, vertex, vs. apply in_seq. lia.
Qed.

Lemma N_VS: forall v,
  v < f.(n) <-> vertex f.(g) v.
Proof.
  intro. unfold vertex. rewrite f.(VS), in_seq. lia.
Qed.

Lemma new_vertices_1: forall v,
  v < f.(n) ->
  vertex transl_graph (set_v_pc v) /\
  vertex transl_graph (live_pc v) /\
  vertex transl_graph (instr_1_pc v) /\
  vertex transl_graph (instr_2_pc v) /\
  vertex transl_graph (set_v_targ_new_pc v) /\
  vertex transl_graph (set_v_targ_pc v) /\
  vertex transl_graph (closing_pc v).
Proof.
  intros. repeat split; apply transl_vertex; unfold_pcs; lia.
Qed.

Lemma new_vertices_2: forall v,
  v < num_regs + f.(n) + 2 ->
  vertex transl_graph (new_entry + v).
Proof.
  intros. apply transl_vertex. unfold_pcs. lia.
Qed.

(* General filter helper lemmata *)

Ltac proceed'' := 
  auto; try easy; try unfold_tuples; simpl in *; unfold_all_edges; unfold_all_pcs; try rewrite VS; try lia.
  
Ltac proceed' := proceed'';
  match goal with
    | [ H: In _ (map _ _) |- _ ] => apply list_in_map_inv in H as [?[?]]
    | [ H: In _ (flat_map _ _) |- _ ] => apply in_flat_map in H as [?[?]]
    | [ H: (filter _ _) = nil |- _ ] => apply filter_nil in H as [?[?]]
    | [ H: (filter _ (_ ++ _)) = _ |- _ ] => rewrite filter_app in H
    | [ H: (map _ (_ ++ _)) = _ |- _ ] => rewrite map_app in H
    | [ |- In _ (map _ _) ] => apply in_map; intros
    | [ |- In _ (flat_map _ _) ] => apply in_flat_map; intros
    | [ |- (filter _ _) = nil ] => apply filter_nil; intros
    | [ |- (filter _ (_ ++ _)) = _ ] => rewrite filter_app 
    | [ |- (map _ (_ ++ _)) = _ ] => rewrite map_app
    | [ x: (?t1 * ?t2)%type |- _ ] => destruct x
    | [ H: In _ (seq _ _) |- _ ] => apply in_seq in H
    | [ |- In _ (seq _ _) ] => apply in_seq
    | [ H: ?a =? ?b = true |- _ ] => apply Nat.eqb_eq in H
    | [ H: ?a =? ?b = false |- _ ] => apply Nat.eqb_neq in H
    | [ |- ?a =? ?b = true ] => apply Nat.eqb_eq
    | [ |- ?a =? ?b = false ] => apply Nat.eqb_neq
    | _ => fail
  end;
  try proceed'; try symmetry; try symmetry in *; try proceed'.

Ltac proceed := proceed''; try proceed'; try symmetry; try symmetry in *; try proceed'.

Lemma filter_seq_single: forall v n v1 v2,
  v >= v1 -> v < v1 + n ->
  filter (fun '(a,b) => a=?v) (map (fun x => (v1+x,v2+x)) (seq 0 n)) = (v, v+v2-v1)::nil.
Proof.
  intros. induction n. lia.
  rewrite seq_S, map_app, filter_app. simpl.
  case (Nat.eq_dec v (v1+n)) eqn:?.
  * replace (v1 + n =? v) with true by (symmetry; rewrite Nat.eqb_eq; lia).
    replace (filter _ _) with (nil : list (nat*nat)%type). simpl. f_equal. apply pair_equal_spec. lia.
    symmetry. apply filter_nil. intros. destruct x. apply list_in_map_inv in H1 as [?[]]. unfold_tuples. apply Nat.eqb_neq. rewrite in_seq in H2. lia.
  * rewrite IHn; [|lia]. now replace (v1 + n =? v) with false by (symmetry; rewrite Nat.eqb_neq; lia).
Qed.

Lemma filter_seq_single_abstr: forall v n v1 v2 f g,
  v >= v1 -> v < v1 + n ->
  (forall x y: nat, f (x,y) = (x=?v)) ->
  (forall x, g x = (v1+x, v2+x)) ->
  filter f (map g (seq 0 n)) = (v, v+v2-v1)::nil.
Proof.
  intros.
  replace (filter _ _) with (filter (fun '(a,b) => a=?v) (map (fun x => (v1+x,v2+x)) (seq 0 n))).
  * now rewrite filter_seq_single.
  * rewrite map_ext with (g:=g).
    apply filter_ext. intros. destruct a. now rewrite H1.
    intros. now rewrite H2.
Qed.

Lemma filter_seq_single_zero: forall v n v2,
  v < n ->
  filter (fun '(a,b) => a=?v) (map (fun x => (x,v2+x)) (seq 0 n)) = (v, v+v2)::nil.
Proof.
  intros. rewrite filter_seq_single_abstr with (v:=v) (v1:=0) (v2:=v2); auto; try lia.
  * f_equal. apply pair_equal_spec. lia.
Qed.

Lemma filter_flatmap_single: forall A B (l: list A) (f: A -> list B) (g: B -> bool) v,
  NoDup l -> In v l -> (forall x y, In x l -> In y (f x) -> (g y = true <-> x = v)) ->
  filter g (flat_map f l) = f v.
Proof.
  intros. induction l. easy.
  destruct H0.
  * simpl. rewrite filter_app. replace (f0 v) with (f0 v ++ nil) by apply app_nil_r. f_equal.
    + subst. apply filter_same. intros. apply H1 in H0; [firstorder|apply in_eq].
    + proceed. apply H1 in H3; auto. enough (x0 <> v).
    - symmetry. apply not_true_is_false. firstorder.
    - apply NoDup_cons_iff in H as []. congruence.
  * simpl. rewrite filter_app, IHl. replace (f0 v) with (nil ++ f0 v) at 2 by auto. f_equal.
    + apply filter_nil. intros. apply H1 in H2. apply not_true_is_false. intro. apply H2 in H3.
      apply NoDup_cons_iff in H as []. congruence. apply in_eq.
    + now apply NoDup_cons_iff in H as [].
    + auto.
    + intros. apply H1. now apply in_cons. auto.
Qed.

(* Edges spec *)

Lemma in_edges_for_vs: forall u v,
  In (u, v) edges_for_vs -> u < 7 * f.(n).
Proof.
  intros. proceed. rewrite f.(VS) in H. repeat (apply in_app in H; destruct H); proceed.
Qed.

Lemma in_edges_vertices: forall u v,
  In (u, v) (edges_for_vs ++ edges_for_regs) -> u < new_N /\ v < new_N.
Proof.
  intros. apply in_app in H. destruct H.
  * proceed. rewrite f.(VS) in H. repeat (apply in_app in H; destruct H); proceed.
    enough (x0 < f.(n)) by lia. apply N_VS. apply successors_spec in H1. auto. now apply N_VS.
  * proceed. destruct H. pose proof f.(ENTRY). apply N_VS in H0. proceed. proceed.
Qed.

Lemma edges_filter_indec_same:
  (edges_for_vs ++ edges_for_regs) =
  filter (fun '(_, w) => in_dec Nat.eq_dec w (seq 0 new_N)) (edges_for_vs ++ edges_for_regs).
Proof.
  rewrite filter_same. auto. intros. destruct x. apply in_edges_vertices in H.
  case in_dec eqn:?. auto. exfalso. apply n1. rewrite in_seq. lia.
Qed.


Lemma new_edges_1: forall v,
  v < f.(n) ->
  set_v_pc v → live_pc v in transl_graph /\
  live_pc v → instr_1_pc v in transl_graph /\
  instr_1_pc v → instr_2_pc v in transl_graph /\
  instr_2_pc v → set_v_targ_new_pc v in transl_graph /\
  set_v_targ_new_pc v → set_v_targ_pc v in transl_graph /\
  set_v_targ_pc v → closing_pc v in transl_graph.
Proof.
  pose proof new_vertices_1.
  intros. unfold transl_graph, es; unfold_edges. rewrite f.(VS).
  repeat split; try apply H; auto.
  all: apply in_app; left.
  6: apply in_app; right. 5-6: apply in_app; right. 4-6: apply in_app; right. 3-6: apply in_app; right. 2-6: apply in_app; right.
  all: apply in_app; left.
  * apply in_map with (f := (fun pc => (set_v_pc pc, live_pc pc))); rewrite in_seq; lia.
  * apply in_map with (f := (fun pc => (live_pc pc, instr_1_pc pc))); rewrite in_seq; lia.
  * apply in_map with (f := (fun pc => (instr_1_pc pc, instr_2_pc pc))); rewrite in_seq; lia.
  * apply in_map with (f := (fun pc => (instr_2_pc pc, set_v_targ_new_pc pc))); rewrite in_seq; lia.
  * apply in_map with (f := (fun pc => (set_v_targ_new_pc pc, set_v_targ_pc pc))); rewrite in_seq; lia.
  * apply in_map with (f := (fun pc => (set_v_targ_pc pc, closing_pc pc))); rewrite in_seq; lia.
Qed.

Ltac rename' x := let y := fresh in rename x into y.

Lemma new_successors_1_single': forall v,
  v < 6 * f.(n) ->
  filter (fun '(x,y) => x =? v) (edges_for_vs ++ edges_for_regs) = (v,v+f.(n))::nil.
Proof.
  intros. rewrite filter_app.
  match goal with [ |- ?l1 ++ ?l2 = _ ] => assert (l2 = nil) end.
  * simpl. case v eqn:?.
    apply filter_nil. intros. destruct x.
    apply list_in_map_inv in H0 as [?[]]. unfold_tuples. apply Nat.eqb_neq. unfold_all_pcs. lia.
    intros. case Nat.eqb eqn:?; [unfold_all_pcs; apply Nat.eqb_eq in Heqb; lia|].
    apply filter_nil. intros.
    unfold_all_pcs. destruct x. apply Nat.eqb_neq. apply list_in_map_inv in H0 as [?[]]. unfold_tuples. lia.
  * rewrite H0. rewrite app_nil_r.
    unfold_edges. unfold_pcs. rewrite f.(VS). repeat rewrite filter_app.
    
    Ltac solve_single := rewrite filter_seq_single; [f_equal; apply pair_equal_spec; lia | lia | lia].
    Ltac solve_single' := rewrite filter_seq_single_zero; [f_equal; apply pair_equal_spec; lia | lia].
    Ltac solve_nil := let x := fresh in let H := fresh in let G := fresh in
      apply filter_nil; intros x H; destruct x; apply list_in_map_inv in H as [?[? G]]; unfold_tuples; rewrite in_seq in G; apply Nat.eqb_neq; lia.
    Ltac solve_nil_flatmap := let x := fresh in let H := fresh in let G := fresh in let H := fresh in
      apply filter_nil; intros x H; destruct x; apply in_flat_map in H as [?[? G]]; apply list_in_map_inv in G as [?[? H]]; unfold_tuples; apply Nat.eqb_neq; lia. 

    case (lt_dec v (1*f.(n))) eqn:?.
      replace ((v,v+f.(n))::nil) with (((v,v+f.(n))::nil)++nil++nil++nil++nil++nil++nil) by auto.
      repeat f_equal; try solve_single'; try solve_nil; solve_nil_flatmap.
    clear Heqs. rename' n.
    case (lt_dec v (2*f.(n))) eqn:?.
      replace ((v,v+f.(n))::nil) with (nil++((v,v+f.(n))::nil)++nil++nil++nil++nil++nil) by auto.
      repeat f_equal; try solve_single; try solve_nil; solve_nil_flatmap.
    clear Heqs. rename' n.
    case (lt_dec v (3*f.(n))) eqn:?.
      replace ((v,v+f.(n))::nil) with (nil++nil++((v,v+f.(n))::nil)++nil++nil++nil++nil) by auto.
      repeat f_equal; try solve_single; try solve_nil; solve_nil_flatmap.
    clear Heqs. rename' n.
    case (lt_dec v (4*f.(n))) eqn:?.
      replace ((v,v+f.(n))::nil) with (nil++nil++nil++((v,v+f.(n))::nil)++nil++nil++nil) by auto.
      repeat f_equal; try solve_single; try solve_nil; solve_nil_flatmap.
    clear Heqs. rename' n.
    case (lt_dec v (5*f.(n))) eqn:?.
      replace ((v,v+f.(n))::nil) with (nil++nil++nil++nil++((v,v+f.(n))::nil)++nil++nil) by auto.
      repeat f_equal; try solve_single; try solve_nil; solve_nil_flatmap.
    clear Heqs. rename' n.
      replace ((v,v+f.(n))::nil) with (nil++nil++nil++nil++nil++((v,v+f.(n))::nil)++nil) by auto.
      repeat f_equal; try solve_single; try solve_nil; solve_nil_flatmap.
Qed.

Lemma new_successors_1_single: forall v,
  v < 6 * f.(n) ->
  length (successors transl_graph v) = 1.
Proof.
  intros. unfold transl_graph, successors, vertex_dec, es, vs.
  erewrite map_length, filter_filter, new_successors_1_single'; eauto.
  Unshelve. 3: { intros [v' w]. exact (in_dec Nat.eq_dec w (seq 0 new_N)). }
  * unfold filter. unfold_all_pcs.
    case in_dec eqn:?. auto.
    exfalso. apply n, in_seq. lia.
  * intros.
    destruct x. rewrite andb_comm. assert ((v =? n) = (n =? v)) by apply Nat.eqb_sym.
    now rewrite H0.
Qed.

Lemma new_successors_1: forall v,
  v < f.(n) ->
  successors transl_graph (set_v_pc v) = live_pc v :: nil /\
  successors transl_graph (live_pc v) = instr_1_pc v :: nil /\
  successors transl_graph (instr_1_pc v) = instr_2_pc v :: nil /\
  successors transl_graph (instr_2_pc v) = set_v_targ_new_pc v :: nil /\
  successors transl_graph (set_v_targ_new_pc v) = set_v_targ_pc v :: nil /\
  successors transl_graph (set_v_targ_pc v) = closing_pc v :: nil.
Proof.
  pose proof new_vertices_1. pose proof new_edges_1.
  intros. repeat split.
  Ltac solve' H H0 := match goal with [ |- successors transl_graph (?pc1 ?v) = ?pc2 ?v :: nil ] =>
    let S := fresh in assert (S: pc1 v < 6 * f.(n)) by (unfold_all_pcs; lia); apply new_successors_1_single in S;
    let I := fresh in assert (I: In (pc2 v) (successors transl_graph (pc1 v))) by (apply successors_spec; [apply H | apply H0]; lia);
    destruct successors as [l|] in *; [easy|]; case l in *; simpl in *; f_equal; lia end.
  Set Warnings "-tactics". (* suppress weird unused-intro-pattern warning *)
  all: solve' H H0.
  Set Warnings "tactics".
Qed.

Lemma new_successors_2': forall v,
  v < f.(n) ->
  filter (fun '(x,y) => (closing_pc v) =? x) (edges_for_vs ++ edges_for_regs) = map (fun s => (closing_pc v, s)) (successors f.(g) v).
Proof.
  intros. proceed.
  remember (map _ (successors f.(g) v)) as res.
  replace res with (res++nil) by apply app_nil_r.
  f_equal.
  * replace res with (nil++nil++nil++nil++nil++nil++res) by auto.
    repeat rewrite filter_app. repeat f_equal; proceed.
    + rewrite filter_flatmap_single with (v:=v); proceed. apply seq_NoDup. split; intro; proceed.
  * simpl. case (_ =? _) eqn:?.
    + pose proof num_regs_nonzero. proceed.
    + proceed.
Qed.

Lemma new_successors_2: forall v,
  v < f.(n) ->
  successors transl_graph (closing_pc v) = successors f.(g) v.
Proof.
  intros. remember (successors f.(g) v) as res.
  unfold transl_graph, successors, vertex_dec, es, vs.
  rewrite filter_filter with
    (g := fun '(v', w) => (closing_pc v =? v'))
    (h := fun '(v', w) => proj_sumbool (in_dec Nat.eq_dec w (seq 0 new_N))).
  match goal with [ |- map _ (filter _ (filter ?g ?e)) = _ ] => replace (filter g e) with e end.
  * rewrite new_successors_2'; [|lia]. now rewrite Heqres, map_map, map_id.
  * apply edges_filter_indec_same.
  * proceed.
Qed.

Lemma new_edges_2: forall v w,
  v → w in f.(g) ->
  closing_pc v → w in transl_graph.
Proof.
  intros. assert (v < f.(n)) by enow apply N_VS.
  apply successors_spec.
  * now apply new_vertices_1.
  * rewrite new_successors_2; auto. now apply successors_spec; try apply N_VS.
Qed.

Lemma new_successors_3': forall v,
  v < num_regs + f.(n) + 1 ->
  filter (fun '(x,y) => (new_entry + v) =? x) (edges_for_vs ++ edges_for_regs) = (new_entry + v, new_entry + S v) :: nil.
Proof.
  intros. remember (_ + _, _ + _) as res. proceed.
  replace ((n,n0)::nil) with (nil++((n,n0)::nil)) by auto.
  f_equal.
  * pose proof num_regs_nonzero. proceed.
    match goal with [ H: In (n1, n2) ?f |- _ ] => replace f with edges_for_vs in H end.
    + apply in_edges_for_vs in H3. proceed.
    + proceed.
  * case (_ =? _) eqn:?.
    + proceed.
    + rewrite filter_seq_single_abstr with (v:=n) (v1:=7*f.(PredRTL.n)) (v2:=7*f.(PredRTL.n)+1); proceed.
      - f_equal. apply pair_equal_spec. lia.
      - rewrite H0. apply Nat.eqb_sym.
      - apply pair_equal_spec. lia.
Qed.

Lemma new_successors_3: forall v,
  v < num_regs + f.(n) + 1 ->
  successors transl_graph (new_entry + v) = new_entry + S v :: nil.
Proof.
  intros.
  unfold transl_graph, successors, vertex_dec, es, vs.
  rewrite filter_filter with
    (g := fun '(v', w) => (init_reg_pc v =? v'))
    (h := fun '(v', w) => proj_sumbool (in_dec Nat.eq_dec w (seq 0 new_N))); [|proceed].
  match goal with [ |- map _ (filter _ (filter ?g ?e)) = _ ] => replace (filter g e) with e end;
  [now rewrite new_successors_3' | apply edges_filter_indec_same].
Qed.

Lemma new_successors_3_init_last:
  successors transl_graph (init_reg_pc (num_regs - 1)) = init_targ_new_pc :: nil.
Proof.
  unfold_all_pcs. rewrite new_successors_3. f_equal. pose num_regs_nonzero. proceed. proceed.
Qed.

Lemma new_successors_3_targ_new:
  successors transl_graph init_targ_new_pc = init_targ_pc :: nil.
Proof.
  unfold_all_pcs. rewrite new_successors_3. f_equal. proceed. proceed.
Qed.

Lemma new_successors_3_targ:
  successors transl_graph init_targ_pc = const_reg_pc 0 :: nil.
Proof.
  unfold_all_pcs. replace (S (7*f.(n)+num_regs)) with (7*f.(n)+(S num_regs)) by lia. rewrite new_successors_3. f_equal. proceed. pose f.(N). proceed.
Qed.

Lemma new_edges_3: forall v,
  v < num_regs + f.(n) + 1 ->
  (new_entry + v) → (new_entry + S v) in transl_graph.
Proof.
  intros. apply successors_spec.
  * apply new_vertices_2. lia.
  * rewrite new_successors_3. unfold init_reg_pc. replace (v+1) with (S v) by lia. apply in_eq. lia.
Qed.

Lemma simpl_filter: forall A f (x:A) xs,
  filter f (x::xs) = if f x then x :: filter f xs else filter f xs.
Proof.
  auto.
Qed.

Lemma simpl_map: forall A B (f: A -> B) x xs,
  map f (x::xs) = (f x) :: map f xs.
Proof.
  auto.
Qed.

Lemma new_successors_4:
  successors transl_graph (new_N - 1) = f.(entry) :: nil.
Proof.
  intros. unfold transl_graph, successors, vertex_dec, vs, es.
  rewrite filter_app, map_app.
  replace (entry f::nil) with (nil++entry f::nil) by auto. f_equal.
  * eenough (H: filter _ _ = nil) by now rewrite H.
    apply filter_nil. intros. destruct x.
    apply in_edges_for_vs in H. apply andb_false_iff. left. apply Nat.eqb_neq. proceed.
  * unfold_edges. rewrite simpl_filter. replace (_ =? _) with true by (symmetry; now apply Nat.eqb_eq).
    replace (proj_sumbool _) with true. 2: { case in_dec; auto. intro. exfalso. apply n. pose proof f.(ENTRY). apply N_VS in H. unfold_pcs. apply in_seq. lia. }
    replace (true && true) with true by auto. rewrite simpl_map. unfold snd at 1. f_equal. eenough (H: filter _ _ = nil) by now rewrite H.
    proceed. symmetry. rewrite andb_false_iff. left. proceed. case n eqn:?; proceed.
Qed.

Lemma new_edges_4:
  (new_N - 1) → f.(entry) in transl_graph.
Proof.
  intros. pose proof num_regs_nonzero. apply successors_spec. 
  * replace (new_N-1) with (new_entry + (num_regs + f.(n) + 1)). apply new_vertices_2. lia. proceed.
  * rewrite new_successors_4. apply in_eq.
Qed.


Lemma edge_path: forall v w,
  v → w in f.(g) ->
  v →( set_v_pc v :: live_pc v :: instr_1_pc v :: instr_2_pc v :: set_v_targ_new_pc v :: set_v_targ_pc v :: closing_pc v :: w :: nil )→* w in transl_graph.
Proof.
  intros.
  assert (v < f.(n)) by enow apply N_VS.
  econstructor 2. now apply new_edges_1.
  econstructor 2. now apply new_edges_1.
  econstructor 2. now apply new_edges_1.
  econstructor 2. now apply new_edges_1.
  econstructor 2. now apply new_edges_1.
  econstructor 2. now apply new_edges_1.
  econstructor 2. enow apply new_edges_2.
  constructor 1.
  unfold vertex, transl_graph, vs, new_N. rewrite in_seq. assert (w < f.(n)) by enow apply N_VS. lia.
Qed.


(*** Welltypedness & Definedness ***)


(*** Properties about the translation ***)

Lemma ncode_new: forall pc,
  transl_code @! pc <> None <-> pc < new_N.
Proof.
  intros. unfold transl_code. unfold_pcs. rewrite to_tree_spec.
  rewrite nth_error_None. repeat rewrite app_length.
  pose proof instrs_lengths. lia.
Qed.

Lemma pc_inv_1: forall pc,
  pc < 7 * f.(n) ->
  exists v,
  v < f.(n) /\
  (pc = set_v_pc v \/ pc = live_pc v \/ pc = instr_1_pc v \/ pc = instr_2_pc v \/ pc = set_v_targ_new_pc v \/ pc = set_v_targ_pc v \/ pc = closing_pc v).
Proof.
  intros. proceed.
  destruct (lt_dec pc (1*f.(n))).
    exists pc. lia.
  rename' n. case (lt_dec pc (2*f.(n))); intro.
    exists (pc-f.(n)). lia.
  rename' n. case (lt_dec pc (3*f.(n))); intro.
    exists (pc-2*f.(n)). lia.
  rename' n. case (lt_dec pc (4*f.(n))); intro.
    exists (pc-3*f.(n)). lia.
  rename' n. case (lt_dec pc (5*f.(n))); intro.
    exists (pc-4*f.(n)). lia.
    rename' n. case (lt_dec pc (6*f.(n))); intro.
    exists (pc-5*f.(n)). lia.
  rename' n. exists (pc-6*f.(n)). lia.
Qed.

Lemma pc_inv_2: forall pc,
  pc >= 7 * f.(n) -> pc < new_N ->
  exists v, v < num_regs + f.(n) + 2 /\ pc = new_entry + v.
Proof.
  intros. exists (pc-7*f.(n)). proceed.
Qed.

Lemma pc_inv_2': forall pc,
  pc >= 7 * f.(n) -> pc < new_N ->
    (exists v, v < num_regs /\ pc = init_reg_pc v) \/
    pc = init_targ_new_pc \/
    pc = init_targ_pc \/
    (exists v, v < f.(n) /\ pc = const_reg_pc v).
Proof.
  intros. destruct (lt_dec pc init_targ_new_pc).
    left. exists (pc-7*f.(n)). proceed.
  destruct (Nat.eq_dec pc init_targ_new_pc). auto.
  destruct (Nat.eq_dec pc init_targ_pc). auto.
    repeat right. exists (pc-7*f.(PredRTL.n)-num_regs-2). proceed.
Qed.

Lemma succs_single_regs: forall v i,
  v < num_regs + f.(n) + 2 ->
  transl_code @! (new_entry + v) = Some i ->
  num_successors i = 1.
Proof.
  intros.
  case (lt_dec v num_regs) eqn:?.
    rewrite new_code_spec_2 in H0; try lia.
    injection H0; intro X; rewrite <- X. unfold init_reg. now case in_dec, (env f (Pos.of_succ_nat v)).
  case (Nat.eq_dec v (num_regs)) eqn:?.
    replace (new_entry + v) with init_targ_new_pc in * by proceed.
    rewrite new_code_spec_3 in H0.
    injection H0; intro X; rewrite <- X. now unfold set_int_reg.
  case (Nat.eq_dec v (num_regs+1)) eqn:?.
    replace (new_entry + v) with init_targ_pc in * by proceed. 
    rewrite new_code_spec_4 in H0.
    injection H0; intro X; rewrite <- X. now unfold set_int_reg.
  replace (new_entry + v) with (const_reg_pc (v-num_regs-2)) in * by proceed.
    rewrite new_code_spec_5 in H0; try lia.
    injection H0; intro X; rewrite <- X. now unfold set_int_reg.
Qed.

Lemma succs_new: forall pc i,
  transl_code @! pc = Some i -> length (successors transl_graph pc) = num_successors i.
Proof.
  intros. assert (pc < new_N) by (apply ncode_new; congruence).
  case (lt_dec pc (7*f.(n))); intro.
  * apply pc_inv_1 in l as [v [S PC]]. decompose [and] (new_successors_1 v S). pose proof (new_successors_2 v S). decompose [and] (new_code_spec_1 v S).
    decompose [or] PC;
    match goal with [ P: pc = ?w v, H: transl_code @! pc = Some i, H': transl_code @! (?w v) = _, S: successors transl_graph (?w v) = _ |- _ ] =>
      copy H; rewrite P, H' in H; injection H; intro X; rewrite <- X;
      rewrite P, S; simpl; try lia
    end.
    - unfold exec_instr_1. case (f.(code) @! v) eqn:?. case uni_dec; now case i0. auto.
    - unfold exec_instr_2. case (f.(code) @! v) eqn:?. case uni_dec; now case i0. auto.
    - unfold set_v_targ_new_instr. case (successors f.(g_pred) v) eqn:?. auto. case l eqn:?. auto. case l0; auto.
    - unfold closing_instr. case (f.(code) @! v) eqn:?; [| now apply f.(NCODE) in Heqo].
      case i0 eqn:?; try (apply f.(SUCCS_G) in Heqo; simpl in *; lia).
      case uniform_cond eqn:?.
      + simpl. copy Heqo. apply f.(SUCCS_COND) in Heqo. apply f.(SUCCS_G) in Heqo0. simpl in Heqo0.
        enough (length (successors f.(g) v) <> 1) by lia. intro. apply Heqo in H17. congruence.
      + simpl. apply f.(SUCCS_COND) in Heqo. now apply Heqo in Heqb.
  * apply pc_inv_2 in H0 as [v [? PC]]; [|lia].
    copy H0. eapply succs_single_regs in H0; eauto. 2: { rewrite PC in H. exact H. }
    rewrite H0.
    case (Nat.eq_dec v (num_regs+f.(PredRTL.n)+1)) eqn:?.
    + replace pc with (new_N - 1). rewrite new_successors_4. auto. proceed.
    + rewrite PC. rewrite new_successors_3. auto. proceed.
Qed.

Lemma entry_new: vertex transl_graph new_entry.
Proof.
  pose proof num_regs_nonzero. unfold vertex. unfold transl_graph, vs. apply in_seq. proceed.
Qed.

Lemma return_instr: forall r v,
  transl_code @! v = Some (Ireturn r) ->
  v = closing_pc f.(exit).
Proof.
  intros.
  assert (v < new_N) by (apply ncode_new; congruence).
  assert (exit f < f.(n)) by (destruct (f.(EXIT) f.(exit)); pose proof (H1 eq_refl) as []; now apply N_VS).
  case (lt_dec v (7*f.(n))) eqn:?. copy l.
  apply pc_inv_1 in l0 as [w[]].
  apply new_code_spec_1 in H2. decompose [and] H2.
  decompose [or] H3;
  match goal with [ P: v = ?g ?w, H: transl_code @! v = Some ?r, H': transl_code @! (?g ?w) = _ |- _ ] =>
      rewrite P, H' in H; proceed
  end.
  * unfold exec_instr_1 in H; case (f.(code) @! w) in *; try congruence; case i in *; try case uni_dec in *; congruence.
  * unfold exec_instr_2 in H; case (f.(code) @! w) in *; try congruence; case i in *; try case uni_dec in *; congruence.
  * unfold set_v_targ_new_instr in H; case (successors f.(g_pred) w) in *; try congruence. case l0 in *; try congruence. case l0 in *; congruence.
  * unfold closing_instr in H. copy H. case (f.(code) @! w) eqn:?; try congruence. case i eqn:?; try congruence.
    enough (E: is_exit f.(g) w) by (apply f.(EXIT) in E; lia).
    apply f.(SUCCS_G) in Heqo. simpl in Heqo. split. 
    apply N_VS. lia. case (successors f.(g) w) eqn:?; auto. case uniform_cond eqn:?; congruence.
    enough (w = f.(exit)) by lia. apply return_exit. now exists o.
  * apply pc_inv_2 in H0 as [? []]; try lia.
    case (lt_dec x num_regs) eqn:?.
    rewrite H2, new_code_spec_2 in H; try lia.
    unfold init_reg in H. case in_dec, (env f (Pos.of_succ_nat x)) in H; congruence.
    case (Nat.eq_dec x (num_regs)) eqn:?.
    replace v with init_targ_new_pc in * by proceed. 
    rewrite new_code_spec_3 in H. unfold set_int_reg in H. congruence.
    case (Nat.eq_dec x (num_regs+1)) eqn:?.
    replace v with init_targ_pc in * by proceed. 
    rewrite new_code_spec_4 in H. unfold set_int_reg in H. congruence.
    replace v with (const_reg_pc (x-num_regs-2)) in * by proceed.
    rewrite new_code_spec_5 in H. unfold set_int_reg in H. congruence. lia.
Qed.

Lemma exit_new: forall v,
  v = closing_pc (exit f) <-> is_exit transl_graph v.
Proof.
  intros. unfold is_exit.
  assert (exit f < f.(n)) by (destruct (f.(EXIT) f.(exit)); pose proof (H eq_refl) as []; now apply N_VS).
  split; intro.
  * rewrite H0. now split; [ apply new_vertices_1 | rewrite new_successors_2; auto; apply f.(EXIT) ].
  * destruct H0.
    assert (v < new_N) by (now unfold vertex, transl_graph, vs in H0; rewrite in_seq in H0).
    apply ncode_new in H2. case (transl_code @! v) eqn:?; [|congruence].
    copy Heqo. apply succs_new in Heqo. rewrite H1 in Heqo.
    case i eqn:?; simpl in Heqo; try lia.
    enow eapply return_instr.
Qed.

(*** Register typing ***)

Ltac unfold_regs := unfold dummy_reg, const_reg, num_regs, cond_which_reg, livereg, targ_new_reg, targ_reg, v_reg, newmaxreg, maxreg.

Definition new_env: regenv := fun r =>
  if negb (plt maxreg r) then f.(env) r
  else if negb (plt newmaxreg r) then f.(env) (r-maxreg)%positive
  else Tint.

Lemma new_env_spec_1: forall r,
  Ple r maxreg -> new_env r = f.(env) r.
Proof.
  intros. unfold new_env.
  case (plt maxreg r) eqn:?; [extlia|]. auto.
Qed.

Lemma new_env_spec_2: forall r,
  ~ Ple r maxreg -> Ple r newmaxreg -> new_env r = f.(env) (r-maxreg)%positive.
Proof.
  intros. unfold new_env.
  case (plt maxreg r) eqn:?; [|extlia].
  case (plt newmaxreg r) eqn:?; [extlia|]. auto.
Qed.

Lemma new_env_spec_3: forall r,
  ~ Ple r newmaxreg -> new_env r = Tint.
Proof.
  intros. unfold new_env.
  case (plt maxreg r) eqn:?; [|unfold newmaxreg in *; extlia].
  case (plt newmaxreg r) eqn:?; [|extlia]. auto.
Qed.

Lemma new_type_v_reg:
  new_env v_reg = Tint.
Proof.
  rewrite new_env_spec_3. auto. unfold_regs. extlia.
Qed.

Lemma new_type_targ_reg: new_env targ_reg = Tint.
Proof.
  rewrite new_env_spec_3. auto. unfold_regs. extlia.
Qed.

Lemma new_type_targ_new_reg: new_env targ_new_reg = Tint.
Proof.
  rewrite new_env_spec_3. auto. unfold_regs. extlia.
Qed.

Lemma new_type_livereg: new_env livereg = Tint.
Proof.
  rewrite new_env_spec_3. auto. unfold_regs. extlia.
Qed.

Lemma new_type_cond_which_reg: new_env cond_which_reg = Tint.
Proof.
  rewrite new_env_spec_3. auto. unfold_regs. extlia.
Qed.

Lemma new_type_normal_reg: forall r,
  Ple r maxreg -> new_env r = f.(env) r.
Proof.
  intros. now apply new_env_spec_1.
Qed.

Lemma new_type_dummy_reg: forall r,
  Ple r maxreg -> new_env (dummy_reg r) = f.(env) r.
Proof.
  intros. unfold dummy_reg.
  rewrite new_env_spec_2. now replace (maxreg + r - maxreg)%positive with r by extlia.
  extlia. unfold_regs. unfold maxreg in H. extlia.
Qed.

Lemma new_type_const_reg: forall r,
  new_env (const_reg r) = Tint.
Proof.
  intros. rewrite new_env_spec_3. auto. unfold_regs. extlia.
Qed.

Lemma move: forall o, {o = Omove} + {o <> Omove}.
Proof.
  intro. case o; (try now left); now right.
Qed.

Lemma new_env_wt: wt_function new_env transl_code (params f) (sig f).
Proof.
  intros. destruct f.(WELLTYPED).
  constructor; auto.
  * rewrite <- wt_params. apply list_map_exten. intros.
    rewrite new_type_normal_reg. auto. now apply max_reg_function_params.
  * intros. assert (transl_code @! pc <> None) by congruence. apply ncode_new in H0.
    case (lt_dec pc (7*f.(n))) eqn:?. clear Heqs.
    apply pc_inv_1 in l as [x [X]]. pose proof (new_code_spec_1 x X). decompose [and] H2. decompose [or] H1.
    + rewrite H9, H3 in H. injection H; intro A; rewrite <- A. unfold set_v_instr. constructor. congruence. auto. simpl.
      apply new_env_spec_3. unfold_regs. extlia.
    + rewrite H11, H5 in H. injection H; intro A; rewrite <- A. unfold set_live_instr. constructor. congruence.
      simpl. repeat f_equal; apply new_env_spec_3; unfold_regs; extlia.
      simpl. apply new_env_spec_3; unfold_regs; extlia.
    + rewrite H9, H4 in H. injection H; intro A; rewrite <- A. unfold exec_instr_1.
      case (_ @! _) eqn:?; try case i eqn:?; try case uni_dec eqn:?; copy Heqo; try apply wt_instrs in Heqo; inv Heqo; try (constructor; fail).
      - constructor. (* Iop Omove *)
        rewrite new_type_normal_reg, new_type_normal_reg; auto.
          unfold maxreg. eapply max_reg_function_use; eauto. enow simpl.
          unfold maxreg. enow eapply max_reg_function_def; eauto.
      - constructor. auto. (* Iop _ *)
           rewrite <- H15. apply list_map_exten. intros. rewrite new_type_normal_reg. auto. unfold maxreg. enow eapply max_reg_function_use.
           rewrite new_type_normal_reg. auto. unfold maxreg. enow eapply max_reg_function_def.
      - constructor. (* Iop Omove *)
        rewrite new_type_dummy_reg, new_type_normal_reg; auto.
          unfold maxreg. eapply max_reg_function_use; eauto. enow simpl.
          unfold maxreg. enow eapply max_reg_function_def; eauto.
      - constructor. auto. (* Iop _ *)
           rewrite <- H15. apply list_map_exten. intros. rewrite new_type_normal_reg. auto. unfold maxreg. enow eapply max_reg_function_use.
           rewrite new_type_dummy_reg. auto. unfold maxreg. enow eapply max_reg_function_def.
      - constructor. (* Iload *)
           rewrite <- H13. apply list_map_exten. intros. rewrite new_type_normal_reg. auto. unfold maxreg. enow eapply max_reg_function_use.
           rewrite new_type_normal_reg. auto. unfold maxreg. enow eapply max_reg_function_def.
      - constructor. congruence. (* Icond *)
          simpl. rewrite <- H12. apply list_map_exten. intros. rewrite new_type_normal_reg. auto. unfold maxreg. enow eapply max_reg_function_use.
          simpl. apply new_type_cond_which_reg.
    + rewrite H11, H6 in H. injection H; intro A; rewrite <- A. unfold exec_instr_2.
      case (_ @! _) eqn:?; try case i eqn:?; copy Heqo; try apply wt_instrs in Heqo; inv Heqo; try case uni_dec eqn:?; try (constructor; fail);
      (constructor; (* Iop *)
          [ apply new_type_livereg | apply new_type_dummy_reg | apply new_type_normal_reg | apply new_type_normal_reg ];
            unfold maxreg; enow eapply max_reg_function_def).
    + rewrite H9, H7 in H. injection H; intro A; rewrite <- A. unfold set_v_targ_new_instr.
      case successors; [|intros; case l; [|intros; case l0; intros]]; try (constructor; fail).
      - constructor. congruence. auto. apply new_type_targ_new_reg. (* Iop Ointconst *)
      - constructor. apply new_type_cond_which_reg. apply new_type_const_reg. apply new_type_const_reg. apply new_type_targ_new_reg.
    + rewrite H11, H8 in H. injection H; intro A; rewrite <- A. unfold set_v_targ_instr.
      constructor. apply new_type_livereg. apply new_type_targ_new_reg. apply new_type_targ_reg. apply new_type_targ_reg.
    + rewrite H11, H10 in H. injection H; intro A; rewrite <- A. unfold closing_instr.
      case (_ @! _) eqn:?; try case i eqn:?; copy Heqo; try apply wt_instrs in Heqo; inv Heqo; try (econstructor; fail).
      - case uniform_cond; constructor. simpl. f_equal. apply new_type_cond_which_reg.
      - now constructor.
      - econstructor. auto.
        rewrite <- H13. apply new_type_normal_reg. enow (eapply max_reg_function_use; eauto; simpl).
        apply new_type_normal_reg. enow (eapply max_reg_function_use; eauto; simpl).
    + apply pc_inv_2' in H0; [|lia]. decompose [ex and or] H0.
    ++ pose proof (new_code_spec_2 x H1). rewrite <- H3, H in H2. injection H2. intro A; rewrite A. unfold init_reg.
       case in_dec. constructor.
       unfold num_regs in H1. case (env f (Pos.of_succ_nat x)) eqn:?; intro.
       - constructor. congruence. auto. simpl. rewrite A in H. rewrite new_type_normal_reg. auto. extlia.
       - constructor. congruence. auto. simpl. rewrite A in H. rewrite new_type_normal_reg. auto. extlia.
       - constructor. congruence. auto. simpl. rewrite A in H. rewrite new_type_normal_reg. auto. extlia.
       - constructor. congruence. auto. simpl. rewrite A in H. rewrite new_type_normal_reg. auto. extlia.
       - constructor. congruence. auto. simpl. rewrite A in H. rewrite new_type_normal_reg. auto.
         Ltac any_free x H1 H4 Heqt := exploit (f.(ANYFREE) (Pos.of_succ_nat x)); [ unfold maxreg in H1; extlia | intro; rewrite Heqt in H4; inv H4 ].
         any_free x H1 H4 Heqt. any_free x H1 H4 Heqt.
       - constructor. congruence. auto. simpl. rewrite A in H. rewrite new_type_normal_reg. auto.
         any_free x H1 H4 Heqt. any_free x H1 H4 Heqt.
    ++ pose proof new_code_spec_3. rewrite <- H2, H in H1. injection H1. intro A; rewrite A. constructor. congruence. auto. apply new_type_targ_new_reg.
    ++ pose proof new_code_spec_4. rewrite <- H1, H in H2. injection H2. intro A; rewrite A. constructor. congruence. auto. apply new_type_targ_reg.
    ++ pose proof (new_code_spec_5 x H1). rewrite <- H3, H in H2. injection H2. intro A; rewrite A. constructor. congruence. auto. apply new_type_const_reg.
Qed.

(*** Translation function ***)

Program Definition transl_function: res SelRTL.function :=
  OK (SelRTL.mkfunction
    transl_code f.(sig) f.(params) f.(stacksize) f.(taint_attr)
    transl_graph new_entry (closing_pc f.(exit)) new_N _ _ ncode_new succs_new entry_new exit_new
    new_env new_env_wt).
Next Obligation.
  pose proof f.(N). proceed.
Qed.

End Translation.

Definition transl_fundef := transf_partial_fundef transl_function.
Definition transf_program (p: PredRTL.program) : res SelRTL.program := transform_partial_program transl_fundef p.

Ltac unfold_regs := unfold dummy_reg, const_reg, num_regs, cond_which_reg, livereg, targ_new_reg, targ_reg, v_reg, newmaxreg, maxreg.
Ltac unfold_all_regs := unfold dummy_reg, const_reg, num_regs, cond_which_reg, livereg, targ_new_reg, targ_reg, v_reg, newmaxreg, maxreg in *.