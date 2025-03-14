Require Import Common Coqlib Classical Datatypes Permutation.
Require Import AST RTL Memory Registers Maps Values Events Globalenvs Smallstep Op Integers.
Require Import TaintAnalysis.
Require Import Before ListsExtra Graph GraphDual GraphRTL SharedTypes SafeOp SafeOpProof.
Require Import Smallstep Errors Linking.
Require Import TopSortVerif.

Definition convert_instruction (i: RTL.instruction) := match i with
  | RTL.Inop _ => Inop
  | RTL.Iop op args res _ => Iop op args res
  | RTL.Iload chunk addr args dst _ => Iload chunk addr args dst
  | RTL.Icond cond args _ _ => Icond cond args
  | RTL.Ireturn val => Ireturn val
  | _ => Inop
  end.

(* Not all instructions are supported currently *)
Definition rtl_instruction_safe (i: RTL.instruction) := match i with
  | RTL.Inop s => true
  | RTL.Iop op args res s => op_is_safe op
  | RTL.Iload chunk addr args dst s => true
  | RTL.Icond cond args s1 s2 => condition_is_safe cond
  | RTL.Ireturn val => true
  | _ => false
  end.

Lemma conversion_keeps_num_successors: forall i i',
  rtl_instruction_safe i = true ->
  convert_instruction i = i' ->
  num_successors i' = length (successors_instr i).
Proof.
  intros. destruct i;
  try (unfold instruction_okay in H; congruence);
  now unfold convert_instruction in H0; rewrite <- H0; unfold num_successors, successors_instr.
Qed.

Definition successors_inbounds (i: RTL.instruction) (max_pc: positive) :=
  forallb (fun s => s <=? max_pc)%positive (successors_instr i).

Definition succ_edges (f: RTL.function) (pc: nat): list (nat*nat) :=
  let conv s := (pc, Pos_to_pred_nat s) in
  match f.(fn_code) @! pc with
  | None => nil
  | Some i => map conv (successors_instr i)
  end.

Definition convert_rtl_to_graph (f: RTL.function): G :=
  let n := Pos.to_nat (max_pc_function f) in
  let vs := seq 0 n in
  let es := flat_map (succ_edges f) vs in
  mkG vs ltac:(now apply seq_NoDup) es.

(* Prove successors of convert_rtl_to_graph correct *)

Lemma filter_flat_map:
  forall (f: nat -> list (nat*nat)) pc n a F,
  F = filter (fun x => fst x =? pc) (flat_map f (seq a n)) ->
  (forall x e, In e (f x) -> fst e = x) ->
  F = if (a <=? pc) && (pc <? (a+n)) then f pc else nil.
Proof.
  intros f pc. induction n.
   intros. simpl in H. case (a <=? pc) eqn:A, (pc <? a+0) eqn:B. simpl. rewrite Nat.leb_le in A. rewrite Nat.ltb_lt in B. lia.
   now simpl. now simpl. now simpl.
  intros. simpl in H. rewrite filter_app in H.
  remember (filter (fun x => fst x =? pc) (flat_map f (seq (S a) n))) as F'.
  case (a <=? pc) eqn:A, (pc <? a + S n) eqn:B.
  * simpl. rewrite Nat.leb_le in A. rewrite Nat.ltb_lt in B.
      case (a =? pc) eqn:E.
    - rewrite Nat.eqb_eq in E. rewrite E in *.
      rewrite H. erewrite (IHn (S pc) F'). assert (S pc <=? pc = false) by (rewrite leb_iff_conv; lia). rewrite H1. simpl.
      rewrite <- app_nil_end. rewrite filter_same. auto.
      intros. epose proof (H0 pc x _). now apply Nat.eqb_eq. auto. auto.
    - rewrite Nat.eqb_neq in E. assert (S a <= pc) by lia. assert (pc < S a + n) by lia.
      rewrite H. erewrite (IHn (S a) F'). assert (S a <=? pc = true) by (rewrite Nat.leb_le; lia). assert (pc <? S a + n = true) by (rewrite Nat.ltb_lt; lia).
      rewrite H3, H4. simpl. rewrite filter_nil. auto.
      intros. epose proof (H0 a x _). rewrite Nat.eqb_neq. lia. auto. auto.
  * simpl. rewrite Nat.ltb_ge in B. rewrite H. erewrite (IHn (S a) F'). assert (pc <? S a + n = false) by (rewrite Nat.ltb_ge; lia). rewrite H1. rewrite andb_false_r.
    rewrite filter_nil. auto. intros. epose proof (H0 a x _). rewrite Nat.eqb_neq. lia. auto. auto.
  * simpl. rewrite Nat.leb_gt in A. rewrite H. erewrite (IHn (S a) F'). assert (S a <=? pc = false) by (rewrite Nat.leb_gt; lia). rewrite H1. simpl.
    rewrite filter_nil. auto. intros. epose proof (H0 a x _). rewrite Nat.eqb_neq. lia. auto. auto.
  * simpl. rewrite Nat.leb_gt in A. rewrite H. erewrite (IHn (S a) F'). assert (S a <=? pc = false) by (rewrite Nat.leb_gt; lia). rewrite H1. simpl.
    rewrite filter_nil. auto. intros. epose proof (H0 a x _). rewrite Nat.eqb_neq. lia. auto. auto.
  Unshelve. auto. auto. auto. auto. auto.
Qed.

Lemma succ_is_vertex: forall f v x,
  (PTree_Properties.for_all f.(fn_code) (fun _ i => successors_inbounds i (max_pc_function f)) = true) ->
  In x (succ_edges f v) ->
  vertex (convert_rtl_to_graph f) (snd x).
Proof.
  intros. unfold succ_edges in H0. case (fn_code f) @! v eqn:I in H0.
  2: now apply in_nil in H0.
  apply list_in_map_inv with (f:=fun s => (v, Pos_to_pred_nat s)) in H0 as [pc [X IN]].
  rewrite X. unfold snd. unfold vertex. unfold convert_rtl_to_graph, vs. apply in_seq.
  split. lia. simpl.
  rewrite PTree_Properties.for_all_correct in H. pose proof (H (Pos.of_succ_nat v) i I).
  unfold successors_inbounds in H0. rewrite forallb_forall in H0. pose proof (H0 pc IN). rewrite Pos.leb_le in H1.
  unfold Pos_to_pred_nat. lia.
Qed.

Lemma transf_succs:
  forall f pc i,
  (PTree_Properties.for_all f.(fn_code) (fun _ i => successors_inbounds i (max_pc_function f)) = true) ->
  f.(fn_code) @! pc = Some i ->
  successors (convert_rtl_to_graph f) pc = map Pos_to_pred_nat (successors_instr i).
Proof.
  intros. unfold successors. simpl.
  remember (filter (fun '(v', w) => (pc =? v') && vertex_dec (convert_rtl_to_graph f) w) (flat_map (succ_edges f) (seq 0 (Pos.to_nat (max_pc_function f))))) as F.
  remember ((fun '(v,w) => proj_sumbool (vertex_dec (convert_rtl_to_graph f) w)): nat*nat -> bool) as h.
  rewrite filter_filter with (g:=(fun x => fst x =? pc)) (h:=h) in HeqF.
  2: { intros [v w]. rewrite Heqh. now replace (pc =? v) with (v =? pc) by apply Nat.eqb_sym. }
  rewrite filter_same with (f:=h) in HeqF.
  2: {
  intros. apply in_flat_map in H1 as [v []]. rewrite in_seq in H1.
  rewrite Heqh. pose proof (succ_is_vertex f v x H H2). unfold snd in H2. now destruct x, vertex_dec.
  }
  rewrite filter_flat_map with (F:=F) (f:=succ_edges f) (a:=0) (n:=Pos.to_nat (max_pc_function f)) (pc:=pc).
  copy H0. apply max_pc_function_sound in H0. assert (pc <? 0 + Pos.to_nat (max_pc_function f) = true) by (apply Nat.leb_le; extlia).
  assert (0 <=? pc = true) by auto. rewrite H2, H3. simpl.
  unfold succ_edges. rewrite H1. apply map_map. auto.
  intros. unfold succ_edges in H1. case (f.(fn_code) @! x) in H1. apply list_in_map_inv in H1 as [x' []]. now rewrite H1. destruct H1.
Qed.

(*** Required properties of the original RTL function ***)

Definition all_instructions_safe (f: RTL.function) :=
  PTree_Properties.for_all f.(fn_code) (fun _ i => rtl_instruction_safe i) = true.

Definition all_instructions_safe_dec (f: RTL.function): {all_instructions_safe f} + {~all_instructions_safe f}.
Proof.
  unfold all_instructions_safe. decide equality.
Qed.

Definition the_unsafe_instruction (f: RTL.function) :=
  match (PTree.fold (fun res n instr =>
    match (res, rtl_instruction_safe instr) with
      | (None, false) => Some n
      | _ => res
    end) f.(fn_code) None)
  with
    | Some n => n
    | None => 999%positive
  end.

Definition all_successors_inbounds (f: RTL.function) :=
  PTree_Properties.for_all f.(fn_code) (fun _ i => successors_inbounds i (max_pc_function f)) = true.

Lemma all_successors_inbounds_dec (f: RTL.function): {all_successors_inbounds f} + {~all_successors_inbounds f}.
Proof.
  unfold all_successors_inbounds. decide equality.
Qed.

Definition straight (f: RTL.function) :=
  forall i, i < Pos.to_nat (max_pc_function f) -> f.(fn_code) @! i <> None.

Definition straight_dec (f: RTL.function): {straight f} + {~straight f}.
Proof.
  case (forallb (fun i => match f.(fn_code) @! i with Some _ => true | None => false end) (seq 0 (Pos.to_nat (max_pc_function f)))) eqn:F.
  * left. intros i IN. rewrite forallb_forall in F. assert (0 <= i < 0 + Pos.to_nat (max_pc_function f)) as IN' by lia. apply in_seq in IN'. pose proof (F i IN'). destruct (f.(fn_code) @! i); congruence.
  * right. intro. apply eq_true_false_abs in F. auto. unfold straight in H. rewrite forallb_forall. intros. apply in_seq in H0 as []. simpl in H1. pose proof (H x H1). destruct (f.(fn_code) @! x); congruence.
Qed.

Definition unique_exit (f: RTL.function): option nat :=
  match filter (fun i => match snd i with RTL.Ireturn _ => true | _ => false end) (PTree.elements f.(fn_code)) with
  | (i,_)::nil => Some (Pos_to_pred_nat i)
  | _ => None
  end.

Definition the_unique_exit (f: RTL.function) := match unique_exit f with Some a => a | None => 0 end.
Definition has_unique_exit (f: RTL.function) := unique_exit f <> None.
Definition has_unique_exit_dec (f: RTL.function): {has_unique_exit f} + {~has_unique_exit f}.
Proof.
  unfold has_unique_exit. case (unique_exit f); auto. intros. left. congruence.
Qed.

Definition entry_exit_inbounds (f: RTL.function) (exit: nat) :=
  let n := Pos.to_nat (max_pc_function f) in andb (Pos_to_pred_nat f.(fn_entrypoint) <? n) (exit <? n) = true.

Lemma entry_exit_inbounds_dec (f: RTL.function) (exit: nat): {entry_exit_inbounds f exit} + {~ entry_exit_inbounds f exit}.
Proof.
  unfold entry_exit_inbounds. decide equality.
Qed.

Lemma transl_function_ncode: forall f code,
  straight f ->
  code = PTree.map1 convert_instruction (fn_code f) ->
  forall pc, code @! pc <> None <-> pc < Pos.to_nat (max_pc_function f).
Proof.
  intros. split.
  * intros. replace code with (PTree.map1 convert_instruction (fn_code f)) in *; auto.
    rewrite PTree.gmap1 in H1. unfold Coqlib.option_map in H1. case (fn_code f) @! pc eqn:A; try congruence.
    apply max_pc_function_sound in A. extlia.
  * intros. unfold straight in H. specialize H with pc. apply H in H1.
    case (f.(fn_code) @! pc) eqn:H1' in H1; try congruence.
    replace code with (PTree.map1 convert_instruction (fn_code f)) in *; auto.
    rewrite PTree.gmap1. unfold Coqlib.option_map. case (f.(fn_code) @! pc) eqn:C; congruence.
Qed.

Lemma transl_function_num_succs: forall f code,
  code = PTree.map1 convert_instruction (fn_code f) ->
  all_instructions_safe f ->
  all_successors_inbounds f ->
  forall pc i, code @! pc = Some i -> length (successors (convert_rtl_to_graph f) pc) = num_successors i.
Proof.
  intros. rewrite H in *. rewrite PTree.gmap1 in H2. unfold Coqlib.option_map in H1. case (fn_code f) @! pc eqn:A; try (simpl in H2; congruence).
  rewrite transf_succs with (i:=i0); auto. rewrite map_length. injection H2; intro.
  unfold all_instructions_safe in H0. rewrite PTree_Properties.for_all_correct in H0. apply H0 in A.
  symmetry. now apply conversion_keeps_num_successors.
Qed.

Lemma transl_function_entry_correct: forall f entry exit,
  entry_exit_inbounds f exit ->
  entry = fn_entrypoint f ->
  vertex (convert_rtl_to_graph f) (Pos_to_pred_nat entry).
Proof.
  intros. rewrite H0. unfold convert_rtl_to_graph, vertex, vs. rewrite in_seq.
  unfold entry_exit_inbounds in H. apply andb_prop in H as []. apply Nat.ltb_lt in H. lia.
Qed.

Lemma transl_function_exit_correct: forall f code,
  code = PTree.map1 convert_instruction (fn_code f) ->
  straight f ->
  all_instructions_safe f ->
  all_successors_inbounds f ->
  has_unique_exit f ->
  entry_exit_inbounds f (the_unique_exit f) ->
  let n := Pos.to_nat (max_pc_function f) in
  forall v, v = the_unique_exit f <-> is_exit (convert_rtl_to_graph f) v.
Proof.
  intros. apply andb_prop in H4 as [].
  unfold all_instructions_safe in H1. rewrite PTree_Properties.for_all_correct in H1.
  unfold has_unique_exit in H3. assert (exists i, unique_exit f = Some i) as [exit EX]. { case unique_exit eqn:U. now exists n0. congruence. }  assert (the_unique_exit f = the_unique_exit f) as E by auto. unfold the_unique_exit in E at 1. rewrite EX in E.
  unfold unique_exit in EX. case filter eqn:A in EX; try congruence. case l in A, EX; destruct p; try congruence. clear H3. injection EX as H3.
  remember (filter _ _). assert (In (p,i) l) as IN by (rewrite A; apply in_eq). rewrite Heql in IN. apply filter_In in IN as [IN]. case snd eqn:B in H6; try congruence. simpl in B.
  apply PTree.elements_complete in IN. replace p with (Pos.of_succ_nat exit) in IN by (rewrite <- H3; apply succpred). copy IN. apply transf_succs in IN; auto.
  split; intro.
  * unfold is_exit. split.
    + unfold convert_rtl_to_graph, vertex, vs. rewrite in_seq. apply Nat.ltb_lt in H5. lia.
    + rewrite H7, <- E, IN, B. now simpl.
  * assert (v < n). { unfold is_exit, vertex, g, convert_rtl_to_graph, vs in H7. destruct H7. apply in_seq in H7; lia. }
    assert (exists x, (fn_code f) @! v = Some x) as [x]. { unfold straight in H0. apply H0 in H8. destruct ((fn_code f) @! v); try congruence. now exists i0. }
    assert (exists x0, x = RTL.Ireturn x0) as [x0]. { copy H9. apply transf_succs in H9; auto. destruct H7. rewrite H11 in H9. destruct x; try (simpl in H9; apply H1 in H10; simpl in H10; congruence). now exists o0. } 
    assert (In (Pos.of_succ_nat v, RTL.Ireturn x0) l) by (rewrite H10 in *; apply PTree.elements_correct in H9; now rewrite Heql; apply filter_In).
    rewrite A in H11. simpl in H11. destruct H11; try contradiction. unfold_tuples. rewrite <- E. rewrite H11 in H3. now rewrite predsucc in H3.
Qed.

Lemma transl_function_safe: forall f code,
  code = PTree.map1 convert_instruction (fn_code f) ->
  all_instructions_safe f ->
  forall pc i, code @! pc = Some i -> instr_safe i.
Proof.
  intros. rewrite H in *.
  unfold all_instructions_safe in H0. rewrite PTree_Properties.for_all_correct in H0.
  rewrite PTree.gmap1 in H1. unfold Coqlib.option_map in H1. case ((fn_code f) @! pc) eqn:F; [injection H1; intro; subst | congruence].
  apply H0 in F. case i0 in *; inv F; easy.
Qed.

Lemma transl_instr_welltyped: forall f env instr,
  RTLtyping.wt_instr f env instr ->
  wt_instr env f.(fn_sig) (convert_instruction instr).
Proof.
  intros. inv H; enow econstructor.
Qed.

Definition the_typenv (f: RTL.function) := match RTLtyping.type_function f with OK a => a | Error _ => fun _ => Tint end.
Definition has_typenv (f: RTL.function) := match RTLtyping.type_function f with OK _ => True | Error _ => False end.
Definition has_typenv_dec (f: RTL.function): {has_typenv f} + {~has_typenv f}.
Proof.
  unfold has_typenv. case (RTLtyping.type_function f); auto.
Qed.

Lemma transl_function_welltyped: forall f code,
  code = PTree.map1 convert_instruction (fn_code f) ->
  has_typenv f ->
  wt_function (the_typenv f) code f.(fn_params) f.(fn_sig).
Proof.
  intros.
  unfold the_typenv, has_typenv in *. destruct (RTLtyping.type_function f) eqn:T; [|contradiction]. 
  apply RTLtyping.type_function_correct in T. destruct T.
  constructor; auto. intros.
  rewrite H in *. rewrite PTree.gmap1 in H1. unfold Coqlib.option_map in H1. case ((fn_code f) @! pc) eqn:F; [injection H1; intro; subst | congruence].
  eapply transl_instr_welltyped, wt_instrs, F.
Qed.

Definition n_small_dec (n: nat): {n < Z.to_nat 1000} + {~ (n < Z.to_nat 1000)}.
Proof.
  apply lt_dec.
Qed.

Lemma n_small_enough: forall n, n < Z.to_nat 1000 -> n < Z.to_nat Int.modulus.
Proof.
  simpl. lia.
Qed.

Lemma taint_ana_dec taint_f: {result : PMap.t DS.L.t | TaintAnalysis.res taint_f = Some result} + {TaintAnalysis.res taint_f = None}.
Proof.
  destruct TaintAnalysis.res eqn:?. left. now exists t. now right.
Qed.

Definition mem_uniform taint_f TAINT_RES code := forall pc chunk addr args dst,
  code @! pc = Some (Iload chunk addr args dst) -> uni taint_f TAINT_RES pc.

Definition mem_uniform' taint_f TAINT_RES code :=
  PTree_Properties.for_all code
    (fun pc i => match i with Iload _ _ _ _ => uni_dec taint_f TAINT_RES (Pos_to_pred_nat pc) | _ => true end) = true.

Lemma mem_uniform_dec: forall code taint_f TAINT_RES, {mem_uniform' taint_f TAINT_RES code} + {~ mem_uniform' taint_f TAINT_RES code}.
  intros. unfold mem_uniform'. decide equality.
Qed.

Lemma mem_uniform_spec: forall code taint_f TAINT_RES,
  mem_uniform' taint_f TAINT_RES code -> mem_uniform taint_f TAINT_RES code.
Proof.
  unfold mem_uniform, mem_uniform' in *. intros. rewrite PTree_Properties.for_all_correct in H.
  apply H in H0. rewrite predsucc in H0. now case uni_dec in *.
Qed.

Definition the_nonuniform_mem_pc code taint_f TAINT_RES :=
  match (PTree.fold (fun res n instr =>
    match (res, (match instr with Iload _ _ _ _ => uni_dec taint_f TAINT_RES (Pos_to_pred_nat n) | _ => true end)) with
      | (None, false) => Some n
      | _ => res
    end) code None)
  with
    | Some n => n
    | None => 999%positive
  end.

(*** Translation function ***)

Definition transl_function (f: RTL.function): res function :=
  let g := convert_rtl_to_graph f in
  if all_instructions_safe_dec f then
  if all_successors_inbounds_dec f then
  if straight_dec f then
  if has_unique_exit_dec f then
  if entry_exit_inbounds_dec f (the_unique_exit f) then
  if n_small_dec (Pos.to_nat (max_pc_function f)) then
  let top_sort := calc_top_sort g in
  if top_sort_correct_dec (Pos.to_nat (max_pc_function f)) g top_sort then
  if has_typenv_dec f then
  let code := PTree.map1 convert_instruction f.(fn_code) in
  if any_free_regenv_dec (the_typenv f) (max_reg_function code (fn_params f)) then
  let taint_f := Build_taint_func code f.(fn_taint_attr) g (the_unique_exit f) (Pos.to_nat (max_pc_function f))
                 top_sort ltac:(enow eapply top_sort_correct_spec) ltac:(lia) ltac:(auto) ltac:(now apply transl_function_ncode) ltac:(enow eapply transl_function_exit_correct) in
  match taint_ana_dec taint_f with
  | inleft taint =>
    if mem_uniform_dec code taint_f taint then
    OK (mkfunction
         code
         f.(fn_sig)
         f.(fn_params)
         f.(fn_stacksize)
         g
         (Pos_to_pred_nat f.(fn_entrypoint))
         (the_unique_exit f)
         (Pos.to_nat (max_pc_function f))
         top_sort
         ltac:(enow eapply top_sort_correct_spec)
         ltac:(auto)
         ltac:(enow eapply n_small_enough)
         ltac:(auto)
         ltac:(now apply transl_function_ncode)
         ltac:(enow eapply transl_function_num_succs)
         ltac:(enow eapply transl_function_entry_correct)
         ltac:(enow eapply transl_function_exit_correct)
         f.(fn_taint_attr)
         taint
         (TaintAnalysis.uniform_cond taint_f taint)
         ltac:(auto)
         ltac:(now apply transl_function_safe with (f:=f))
         ltac:(enow eapply mem_uniform_spec)
         (the_typenv f)
         ltac:(auto)
         ltac:(enow eapply transl_function_welltyped)
        )
    else Error (MSG "Iload instruction at non-uniform PC " :: POS (the_nonuniform_mem_pc code taint_f taint) :: nil)
  | _ => Error (msg "Taint analysis failed")
  end
  else Error (msg "RTL typcheck contains Tany-types")
  else Error (msg "RTL typecheck failed")
  else Error (msg "Graph contains loops")
  else Error (msg "Graph too large")
  else Error (msg "Entry or exit is out-of-bounds")
  else Error (msg "There are no or multiple return instructions")
  else Error (msg "There is a hole in the RTL code")
  else Error (msg "Instruction has out-of-bounds successor")
  else Error (MSG "Unsupported instruction at PC " :: POS (the_unsafe_instruction f) :: nil).

Definition transl_fundef := transf_partial_fundef transl_function.
Definition transf_program (p: RTL.program) : res GraphRTL.program := transform_partial_program transl_fundef p.

Ltac unfold_matches f TF :=
  let A := fresh "OK" in case all_instructions_safe_dec eqn:A in TF; try congruence;
  let A := fresh "IN" in case all_successors_inbounds_dec eqn:A in TF; try congruence;
  let A := fresh "SD" in case straight_dec eqn:A in TF; try congruence;
  let A := fresh "UE" in case has_unique_exit_dec eqn:A in TF; try congruence;
  let A := fresh "EE" in case entry_exit_inbounds_dec eqn:A in TF; try congruence;
  let A := fresh "NS" in case n_small_dec eqn:A in TF; try congruence;
  let A := fresh "TS" in case top_sort_correct_dec eqn:A in TF; try congruence;
  let A := fresh "TE" in case has_typenv_dec eqn:A in TF; try congruence;
  let A := fresh "AF" in case any_free_regenv_dec eqn:A in TF; try congruence;
  let A := fresh "TA" in case taint_ana_dec eqn:A in TF; try congruence;
  let A := fresh "MU" in case mem_uniform_dec eqn:A in TF; try congruence.

Ltac unfold_tf :=
  match goal with 
   | [ TF: transl_function ?f = OK ?tf |- _ ] =>
     unfold transl_function in TF;
     unfold_matches f TF;
     injection TF; clear TF; intro TF; try rewrite <- TF
  end.

(*** SEMANTIC MATCH AND PRESERVATION ***)

Inductive match_states: RTL.state -> GraphRTL.state -> Prop :=
  | match_state:
      forall f tf sp pc rs rs' m wt def
        (LD: regs_lessdef rs rs')
        (TF: transl_function f = OK tf)
        (SP: exists b ofs, sp = Vptr b ofs),
      match_states (RTL.State nil f sp (Pos.of_succ_nat pc) rs m) (GraphRTL.State tf sp pc rs' m wt def)
  | match_initstate:
      forall args f tf m wt def
        (TF: transl_fundef f = OK tf),
        match_states (RTL.Callstate nil f args m) (GraphRTL.InitState tf args m wt def)
  | match_endstate:
      forall f v v' m
      (LD: Val.lessdef v v'),
      match_states (RTL.Returnstate nil v m) (GraphRTL.EndState f v' m).

Definition match_prog (p: RTL.program) (tp: GraphRTL.program) :=
  match_program (fun cu f tf => transl_fundef f = OK tf) eq p tp.

Lemma transf_program_match: forall p tp, transf_program p = OK tp ->  match_prog p tp.
Proof.
  intros. now apply match_transform_partial_program.
Qed.

Section Preservation.

Variable prog: RTL.program.
Variable tprog: GraphRTL.program.
Hypothesis TRANSL: match_prog prog tprog.

Let ge : RTL.genv := Genv.globalenv prog.
Let tge : GraphRTL.genv := Genv.globalenv tprog.

(* Trivial boilerplate *)

Lemma symbols_preserved:
  forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
Proof (Genv.find_symbol_transf_partial TRANSL).

Lemma senv_preserved:
  Senv.equiv (Genv.to_senv ge) (Genv.to_senv tge).
Proof (Genv.senv_transf_partial TRANSL).

Lemma function_ptr_translated:
  forall (b: block) (f: RTL.fundef),
  Genv.find_funct_ptr ge b = Some f ->
  exists tf,
  Genv.find_funct_ptr tge b = Some tf /\ transl_fundef f = OK tf.
Proof (Genv.find_funct_ptr_transf_partial TRANSL).

Lemma sig_function_translated:
  forall f tf,
  transl_fundef f = OK tf ->
  GraphRTL.funsig tf = RTL.funsig f.
Proof.
  intros. unfold GraphRTL.funsig, RTL.funsig.
  unfold transl_fundef, transf_partial_fundef, bind, transl_function in H.
  case f in *. try congruence.
  unfold_matches f H.
  injection H; intro. rewrite <- H0. now simpl.
  injection H; intro. rewrite <- H0. auto.
Qed.

(* Initial and final states *)

Lemma transl_initial_states:
  forall S, RTL.initial_state prog S ->
  exists R, GraphRTL.initial_state tprog R /\ match_states S R.
Proof.
  intros. inv H.
  exploit function_ptr_translated. eauto. intros [tf [G T]].
  eexists (InitState tf nil m0 _ _). split.
    econstructor.
  - now apply (Genv.init_mem_transf_partial TRANSL).
  - replace (prog_main tprog) with (prog_main prog). rewrite symbols_preserved. eauto.
    symmetry. eapply match_program_main. eauto.
  - exact G.
  - now constructor.
  Unshelve. rewrite <- H3. now apply sig_function_translated.
Qed.

Lemma transl_final_states:
  forall S R r,
  match_states S R -> RTL.final_state S r -> GraphRTL.final_state R r.
Proof.
  intros. inv H0. inv H. inv LD. constructor.
Qed.


(* Step *)

Ltac transfstep :=
  match goal with
   | [ H: (fn_code ?f) @! ?pc = Some ?i |- getinstr ?tf ?pc = Some ?i' ] =>
     unfold_tf; unfold transl_function, getinstr, code; rewrite PTree.gmap1, H; now unfold Coqlib.option_map, convert_instruction
   | [ TF: transl_function ?f = OK ?tf, H: (fn_code ?f) @! ?pc = Some ?i |- uniquesucc ?tf ?pc = Some ?pc' ] =>
     let TF2 := fresh in pose proof TF as TF2; unfold_tf;
     unfold uniquesucc, g; erewrite transf_succs with f pc i; simpl successors_instr; simpl; auto
   | [ TF: transl_function ?f = OK ?tf |- match_states (RTL.State nil ?f ?sp ?pc' ?rs ?m) (State ?tf ?sp (Pos_to_pred_nat ?pc') ?rs' ?m ?wt ?def) ] =>
     let TF2 := fresh in pose proof TF as TF2; unfold_tf;
     set (pc_ := Pos_to_pred_nat pc'); let H := fresh in assert (pc' = Pos.of_succ_nat pc_) as H by (unfold pc_, Pos_to_pred_nat; lia); rewrite H; constructor; try now rewrite TF2
   end.

Lemma instructions_are_safe: forall f tf pc i,
  transl_function f = OK tf ->
  (fn_code f) @! pc = Some i ->
  rtl_instruction_safe i = true.
Proof.
  intros. unfold transl_function in H.
  destruct all_instructions_safe_dec eqn:H'; try congruence.
  unfold all_instructions_safe in a. copy a. rewrite PTree_Properties.for_all_correct in a0. eapply a0; eauto.
Qed.

Theorem transl_step_correct:
  forall s1 t s2, RTL.step ge s1 t s2 ->
  forall ts1 (MS: match_states s1 ts1),
  exists ts2, GraphRTL.step tge ts1 t ts2 /\ match_states s2 ts2.
Proof.
  intros. inv MS.
  + inv H.
  * econstructor; split. constructor 1. transfstep. transfstep. transfstep; auto.
  * (* operation also evals on the more-defined registers to something more-defined *)
    erewrite eval_operation_preserved in H9. eapply eval_operation_lessdef with (m2:=m) (vl2:=rs'##args) in H9 as [v' []].
    2: now apply regs_lessdef_regs. 2: apply Mem.extends_refl. 2: symmetry; apply symbols_preserved.
    (* now construct the state *)
    econstructor; split. econstructor 2.
    remember (wt_exec_Iop _ _ _ _ _ _ _ _ _ _ _ _ _ _).
    remember (op_step_def _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
    Unshelve. 2: exact (Pos_to_pred_nat pc'). 4: exact res.
    all: eauto.
    set (pc_ := Pos_to_pred_nat pc'); let H := fresh in assert (pc' = Pos.of_succ_nat pc_) as H by (unfold pc_, Pos_to_pred_nat; lia); rewrite H.
    constructor.
    - now apply set_reg_lessdef.
    - auto.
    - apply SP.
    - transfstep.
    - transfstep.
  * (* mem load also evals on the more-defined registers to something more-defined *)
    erewrite eval_addressing_preserved in H9; [| symmetry; apply symbols_preserved ].
    eapply eval_addressing_lessdef in H9 as [a' []]; [| now apply regs_lessdef_regs ].
    eapply Mem.loadv_extends in H10 as [v' []]; [| apply Mem.extends_refl | apply H0 ].
    set (pc_ := Pos_to_pred_nat pc'); let H := fresh in assert (pc' = Pos.of_succ_nat pc_) as H by (unfold pc_, Pos_to_pred_nat; lia); rewrite H.
    econstructor; split.
    2: { econstructor 1; eauto. apply set_reg_lessdef; [apply H2 | apply LD]. }
    econstructor 3. Unshelve. 3: exact chunk. 3: exact addr. 3: exact args.
    - transfstep.
    - eauto.
    - transfstep.
    - auto.
  * exploit instructions_are_safe; eauto. simpl. congruence.
  * exploit instructions_are_safe; eauto. simpl. congruence.
  * exploit instructions_are_safe; eauto. simpl. congruence.
  * exploit instructions_are_safe; eauto. simpl. congruence.
  * (* condition also evals on the more-defined registers to something more-defined *)
    eapply eval_condition_lessdef with (m2:=m) (vl2:=rs'##args) in H9.
    2: now apply regs_lessdef_regs. 2: apply Mem.extends_refl.
    (* now construct the state *)
    econstructor; split. econstructor 4. transfstep.
    copy TF. unfold_tf. unfold g. erewrite transf_succs with f pc (RTL.Icond cond args ifso ifnot). simpl successors_instr. simpl. eauto. eauto. eauto. eauto. eauto.
    case b; transfstep; auto.
  * exploit instructions_are_safe; eauto. simpl. congruence.
  * econstructor. split. econstructor 7. transfstep.
    copy TF. unfold_tf. unfold g. erewrite transf_succs with f pc (RTL.Ireturn or); eauto.
    unfold_tf. unfold stacksize. exact H9.
    constructor. case or; easy.
  + inv H.
  * destruct tf; unfold transl_fundef, transf_partial_fundef, bind in TF; case transl_function eqn:TF' in TF; try congruence.
    assert (f1 = f) by now injection TF. rewrite H in *.
    econstructor. split. unfold_tf.
    econstructor 5. replace (stacksize f) with (fn_stacksize f0) by now rewrite <- TF'. eauto. 
    assert (Pos.of_succ_nat (entry f) = (fn_entrypoint f0)) by (unfold_tf; apply succpred). rewrite <- H0.
    constructor. unfold_tf. apply init_all_rtl_lessdef. auto.
    enow eexists.
  * destruct tf; unfold transl_fundef, transf_partial_fundef, bind in TF. congruence.
    econstructor. split.
    replace ef with e in *.
    constructor. eapply external_call_symbols_preserved. apply senv_preserved. eauto.
    now inv TF.
    constructor. auto.
  + inv H.
Qed.

Theorem transf_program_correct:
  forward_simulation (RTL.semantics prog) (GraphRTL.semantics tprog).
Proof.
  eapply forward_simulation_step.
  apply senv_preserved.
  exact transl_initial_states.
  exact transl_final_states.
  exact transl_step_correct.
Qed.

End Preservation.