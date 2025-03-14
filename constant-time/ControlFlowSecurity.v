Require Import Common Coqlib Classical Datatypes.
Require Import AST Memory Registers Maps Values Events Globalenvs Smallstep Op Integers.
Require Import Smallstep Errors.
Require Import ListsExtra Before Permutation GraphRTL.
Require Import Graph GraphDual.
Require Import SharedTypes TaintAnalysis InfluenceRegion PredRTL.
Require Import Coq.Program.Equality.

(* star_tr improves on star in two things: first, it keeps a trace of visited nodes.
   Second, it adds edges from the right instead of from the left to allow induction keeping the start of the path. *)
Inductive star_tr' {ST} {GE} (ge: GE) step get_pc: ST -> list (option nat) -> ST -> Prop :=
  | tr_refl: forall s, star_tr' ge step get_pc s nil s
  | tr_step: forall s1 s2 tr1 (tr2: Events.trace) s3 t,
      star_tr' ge step get_pc s1 tr1 s2 -> step ge s2 tr2 s3 -> t = get_pc s2 :: tr1 ->
      star_tr' ge step get_pc s1 t s3.

Lemma star_tr'_left: forall ST GE (ge: GE) step get_pc (s1 s2 s3: ST) tr1 tr2,
  step ge s1 tr1 s2 -> star_tr' ge step get_pc s2 tr2 s3 ->
  star_tr' ge step get_pc s1 (tr2 ++ get_pc s1 :: nil) s3.
Proof.
  intros. induction H. econstructor 2 with (s2:=s1); eauto. constructor. auto.
  apply IHstar_tr' in X. econstructor 2 with (s2:=s2); eauto. now subst.
Qed.

Lemma star_has_trace: forall ST GE (ge: GE) step get_pc (s1 s2: ST) t,
  star step ge s1 t s2 -> exists tr, star_tr' ge step get_pc s1 tr s2. 
Proof.
  intros. induction H. exists nil. constructor.
  destruct IHstar. exists (x ++ get_pc s1 :: nil). enow eapply star_tr'_left.
Qed.


(* PredRTL-Specific Timing Properties *)

Section Security.

Variable tprog: program.
Let tge : genv := Genv.globalenv tprog.

Variable f: function.

(*** PUBLIC & TAINTED REGS ***)

Definition tainted_reg := tainted_reg f.(taint_f) f.(TAINT_RES).

Definition public reg := tainted_reg reg = false.
Fixpoint public_list regs := match regs with
  | nil => True
  | reg::regs => public reg /\ public_list regs
end.

Lemma public_dec reg: {public reg} + {~ public reg}.
Proof.
  unfold public. destruct tainted_reg. now right. now left.
Qed.

Lemma public_list_dec regs: {public_list regs} + {~ public_list regs}.
  intros. induction regs. now left.
  case IHregs eqn:?.
  * case (public_dec a) eqn:?. now left. right. now simpl.
  * right. now simpl.
Qed.

Lemma public_list_not_spec: forall l,
  ~ public_list l <-> exists x, In x l /\ tainted_reg x = true.
Proof.
  intros. induction l; split; intro.
  * now simpl in H.
  * now destruct H.
  * simpl in H. apply not_and_or in H as [].
    + exists a. split. apply in_eq. unfold public in H. case tainted_reg eqn:?; congruence.
    + apply IHl in H as [x []]. exists x. split. apply in_cons, H. auto.
  * intro. destruct H0. destruct H as [x []]. destruct H.
    + subst. unfold public in H0. congruence.
    + apply IHl in H1. auto. now exists x.
Qed.

Definition agree_publicly (rs1 rs2: regset): Prop :=
  forall r, public r -> rs1 # r = rs2 # r.

Lemma agree_on_public_list: forall rs1 rs2 regs,
  agree_publicly rs1 rs2 ->
  public_list regs ->
  rs1 ## regs = rs2 ## regs.
Proof.
  intros. induction regs. auto.
  simpl. simpl in H0. now f_equal; [ apply H | apply IHregs ].
Qed.

Lemma agree_publicly_sym: forall rs1 rs2,
  agree_publicly rs1 rs2 ->
  agree_publicly rs2 rs1.
Proof.
  unfold agree_publicly. intros. symmetry. now apply H.
Qed.

Lemma agree_publicly_refl: forall rs,
  agree_publicly rs rs.
Proof.
  now unfold agree_publicly.
Qed.

Lemma agree_publicly_assign_same: forall rs1 rs2 r v,
  agree_publicly rs1 rs2 ->
  agree_publicly (rs1 # r <- v) (rs2 # r <- v).
Proof.
  unfold agree_publicly. intros.
  case (peq r r0) eqn:?.
  * now rewrite e, Regmap.gss, Regmap.gss.
  * enow rewrite Regmap.gso, Regmap.gso.
Qed.
  
Lemma agree_publicly_assign_tainted: forall rs1 rs2 r v1 v2,
  agree_publicly rs1 rs2 ->
  ~ public r ->
  agree_publicly (rs1 # r <- v1) (rs2 # r <- v2).
Proof.
  unfold agree_publicly. intros.
  case (peq r r0) eqn:?.
  * now rewrite e in H0.
  * enow rewrite Regmap.gso, Regmap.gso.
Qed.

Lemma agree_publicly_assign_tainted': forall rs1 rs2 r v,
  agree_publicly rs1 rs2 ->
  ~ public r ->
  agree_publicly rs1 (rs2 # r <- v).
Proof.
  unfold agree_publicly. intros.
  case (peq r r0) eqn:?.
  * now rewrite e in H0.
  * enow rewrite Regmap.gso.
Qed.


(*** OTHER DEFS ***)

Definition get_pc (s: state) := match s with
  | State f sp v rs m v_targ pd WT DEF => Some v
  | InitState f args m VL DEF => None
  | EndState f v m => None
end.

Definition get_regs (s: state) := match s with
  | State f sp v rs m v_targ pd WT DEF => Some rs
  | InitState f args m VL DEF => None
  | EndState f v m => None
end.

Definition function (s: state) := match s with
  | State f sp v rs m v_targ pd WT DEF => Internal f
  | InitState f args m VL DEF => f
  | EndState f v m => f
end.

Definition star_tr := star_tr' tge step get_pc.

Definition ipd := ipd f.(g_pred) f.(exit) f.(EXIT') f.(idx) f.(top_sort_pred).
Notation "x ∈ 'ir' ( c )" := (in_ir f.(g_pred) f.(exit) f.(EXIT') f.(idx) f.(top_sort_pred) c x) (at level 50).
Notation "x ∈ 'ir_inn' ( c )" := (x ∈ ir(c) /\ x <> ipd c) (at level 50).

Definition chain_inv := chain_inv f.(g_pred) f.(uniform_cond) f.(exit) f.(EXIT') f.(idx) f.(top_sort_pred).


(*** TAINT THEOREMS ***)

(* The main theorems of taint ana: *)

Lemma taint_ana_instr_uses: forall v i d,
  f.(code) @! v = Some i ->
  instr_defs i = Some d ->
  ~ public_list (instr_uses i) ->
  ~ public d.
Proof.
  intros.
  assert (C: f.(code) = TaintAnalysis.code (taint_f f)) by auto.
  destruct (f.(code) @! v) eqn:?; try destruct i0 eqn:?; try congruence.
  * injection H; intro; rewrite <- H2 in H0. simpl in H0. congruence.
  * injection H; intro; rewrite <- H2 in H0. simpl in H0. injection H0; intro; subst.
    apply public_list_not_spec in H1 as [x []].
    rewrite C in Heqo. eapply taint_ana_respects_reg_use_op in Heqo; eauto. unfold public, tainted_reg. intro. rewrite Heqo in H3. congruence.
  * injection H; intro; rewrite <- H2 in H0. simpl in H0. injection H0; intro; subst.
    apply public_list_not_spec in H1 as [x []].
    rewrite C in Heqo. eapply taint_ana_respects_reg_use_load in Heqo; eauto. unfold public, tainted_reg. intro. rewrite Heqo in H3. congruence.
  * injection H; intro; rewrite <- H2 in H0. simpl in H0. congruence.
  * injection H; intro; rewrite <- H2 in H0. simpl in H0. congruence.
  * apply f.(SAFE) in Heqo. easy.
Qed.

Lemma taint_ana_ir_cond: forall c v i d,
  f.(code) @! v = Some i ->
  instr_defs i = Some d ->
  v ∈ ir_inn(c) ->
  uniform_cond f c = false ->
  ~ public d.
Proof.
  intros. rewrite f.(UNIFORM) in H2.
  assert (C: f.(code) = TaintAnalysis.code (taint_f f)) by auto.
  destruct (f.(code) @! v) eqn:?; try destruct i0 eqn:?; try congruence.
  * injection H; intro; rewrite <- H3 in H0. simpl in H0. congruence.
  * injection H; intro; rewrite <- H3 in H0. simpl in H0. injection H0; intro; subst.
    rewrite C in Heqo. eapply taint_ana_respects_ir in Heqo; auto. unfold public, tainted_reg. rewrite not_false_iff_true. apply Heqo.
    unfold TaintAnalysis.uniform_cond in H2. enow rewrite negb_false_iff in H2. apply H1.
  * apply UNI_MEM in Heqo. exfalso. apply Heqo in H1. auto. unfold TaintAnalysis.uniform_cond in H2. now rewrite negb_false_iff in H2.
  * injection H; intro; rewrite <- H3 in H0. simpl in H0. congruence.
  * injection H; intro; rewrite <- H3 in H0. simpl in H0. congruence.
  * apply f.(SAFE) in Heqo. easy.
Qed.

Lemma uniform_cond_has_clean_params: forall v cond regs,
  f.(code) @! v = Some (Icond cond regs) ->
  uniform_cond f v = true ->
  public_list regs.
Proof.
  intros. rewrite f.(UNIFORM) in H0.
  assert (C: f.(code) = TaintAnalysis.code (taint_f f)) by auto.
  rewrite C in H. destruct (public_list_dec regs) eqn:?; auto.
  exfalso. clear Heqs. apply public_list_not_spec in n as [t []].
  eapply tainted_cond_spec in H2; eauto. unfold TaintAnalysis.uniform_cond in H0. now rewrite H2 in H0. 
Qed.

(*** OUR VERSION OF THM 4.1 ***)

Lemma chain_inv_detour: forall v x w v_targ,
  v → x in f.(g_pred) ->
  w = f.(detour) v x ->
  w <> x ->
  v << v_targ in f.(idx) ->
  chain_inv v v_targ ->
  chain_inv w v_targ.
Proof.
  intros. apply chain_inv_indirect_edge with (v:=v) (w:=w) (x:=x); auto.
  rewrite H0 in H1. apply not_eq_sym, DETOUR_CHAIN in H1; auto. now subst.
Qed.

Lemma target_gives_chain_inv: forall init trace sp v v_targ rs m pd wt def,
  initial_state tprog init ->
  star_tr init trace (State f sp v rs m v_targ pd wt def) ->
  v <> v_targ ->
  chain_inv v v_targ.
Proof.
  intros.
  pose proof f.(top_sort_pred) as P.
  assert (EG: forall e : V, is_exit (g f) e <-> e = exit f). { intros. split; intro; now apply f.(EXIT). }
  dependent induction trace. inv H0; [inv H|congruence].
  inv H0. simpl in *. injection H4; intros. copy H3. inv H3.
  * apply step_is_detour_2 in H6 as [? []]; auto. apply IHtrace in H2; auto.
    assert (v0 << v_targ in f.(idx)) by (eapply postdom_before in PD0; eauto; apply top_sort_g).
    case (Nat.eq_dec v x) eqn:?.
    + subst x. enow eapply chain_inv_direct_edge.
    + now apply chain_inv_detour with (x:=x) (w:=v) (v:=v0).
  * apply step_is_detour_2 in H6 as [? []]; auto. apply IHtrace in H2; auto.
    assert (v0 << v_targ in f.(idx)) by (eapply postdom_before in PD0; eauto; apply top_sort_g).
    case (Nat.eq_dec w0 x) eqn:?.
    + subst x. enow eapply chain_inv_direct_edge.
    + now apply chain_inv_detour with (x:=x) (w:=w0) (v:=v0).
  * apply step_is_detour_1 in H6 as []; auto.
    rewrite H3 in H1. apply not_eq_sym, DETOUR_CHAIN in H1; auto. subst. now apply chain_inv_sym.
  * apply step_is_detour_1 in H6 as []; auto.
    rewrite H3 in H1. apply not_eq_sym, DETOUR_CHAIN in H1; auto. subst. now apply chain_inv_sym.
  * apply step_is_detour_1 in H6 as []; auto.
    rewrite H3 in H1. apply not_eq_sym, DETOUR_CHAIN in H1; auto. subst. now apply chain_inv_sym.
  * apply step_is_detour_1 in H6 as []; auto.
    rewrite H3 in H1. apply not_eq_sym, DETOUR_CHAIN in H1; auto. subst. now apply chain_inv_sym.
  * lia.
Qed.

Lemma target_gives_tainted_ir: forall init trace sp v v_targ rs m pd wt def,
  initial_state tprog init ->
  star_tr init trace (State f sp v rs m v_targ pd wt def) ->
  v <> v_targ ->
  exists c, f.(uniform_cond) c = false /\ v ∈ ir(c).
Proof.
  intros. apply target_gives_chain_inv in H0; auto.
  repeat destruct H0. exists x. split. apply H0, in_eq. easy.
Qed.

Lemma target_gives_tainted_ir_inner: forall init trace sp v v_targ rs m pd wt def,
  initial_state tprog init ->
  star_tr init trace (State f sp v rs m v_targ pd wt def) ->
  v << v_targ in f.(idx) ->
  exists c, f.(uniform_cond) c = false /\ v ∈ ir_inn(c).
Proof.
  intros. apply target_gives_chain_inv in H0; auto.
  * unfold chain_inv, PredRTL.chain_inv in H0. decompose [ex and] H0.
    case (Nat.eq_dec v (ipd x)) eqn:?.
    + subst. apply chain_containment in H6. decompose [ex and] H6.
      exists x2. repeat split; auto. eapply beforeeq_trans_2; eauto.
      eapply top_sort_nodup, top_sort_pred. now apply ir_before.
    + exists x. repeat split; auto. apply H3, in_eq.
  * eapply (before_id_neq Nat.eq_dec); eauto. eapply top_sort_nodup, top_sort_pred.
Qed.

(* This corollary is equivalent to Theorem 4.1 from the paper. *)
Corollary uni_chain_path: forall sp v v_targ rs m pd wt def,
  state_emergent tprog (State f sp v rs m v_targ pd wt def) ->
  v <> v_targ ->
  ~ uni f.(taint_f) f.(TAINT_RES) v.
Proof.
  intros. intro. assert (v << v_targ in f.(idx)). { eapply postdom_before; eauto. apply top_sort_g. split; intro; now apply EXIT. }
  inv H. edestruct star_has_trace with (get_pc:=get_pc) in H4; eauto.
  eapply target_gives_tainted_ir_inner in H3 as [c []]; eauto.
  destruct H1 with (c:=c); auto. rewrite UNIFORM in H3. now rewrite <- negb_false_iff.
Qed.

(*** CONTROL FLOW SECURITY PROOF ***)

Lemma tainted_cond_same_target: forall v w1 w2,
  length (successors f.(g) v) = 1 ->
  v → w1 in f.(g_pred) ->
  v → w2 in f.(g_pred) ->
  f.(detour) v w1 = f.(detour) v w2.
Proof.
  intros.
  destruct (DETOUR_SPEC f v w1 H0). destruct (DETOUR_SPEC f v w2 H1).
  case (successors f.(g) v) eqn:?; [easy|]. case l eqn:?; [|easy].
  apply successors_spec in H2, H4; auto. rewrite Heql in H2, H4. simpl in H2, H4. destruct H2; [|easy]. destruct H4; [|easy].
  now subst.
Qed.

Lemma step_nop_op:
  forall v v_targ1 sp op args v1' v2' w1 w2 m rs1 rs2 r res rs' pd wt def init tr
  (INIT1: initial_state tprog init)
  (INIT2: star_tr init tr (State f sp v rs' m v_targ1 pd wt def))
  (I1: getinstr f v = Some (Iop op args res))
  (U1: uniquesucc f v = Some (v1', w1)) (U2: uniquesucc f v = Some (v2', w2))
  (E1: eval_operation tge sp op rs2 ## args m = Some r),
  v <> v_targ1 ->
  agree_publicly rs1 rs2 ->
  v1' = v2' /\ agree_publicly rs1 (rs2 # res <- r).
Proof.
  intros.
  rewrite U1 in U2. injection U2. intros. split; auto.
  apply agree_publicly_assign_tainted'; auto.
  apply target_gives_tainted_ir_inner in INIT2 as [? []]; auto. enow eapply taint_ana_ir_cond.
  clear INIT2. eapply postdom_before in pd; eauto. apply top_sort_g. split; intro; now apply EXIT.
Qed.

Lemma step_nop_load:
  forall v v_targ1 sp chunk addr args dst m rs' pd wt def init tr
  (INIT1: initial_state tprog init)
  (INIT2: star_tr init tr (State f sp v rs' m v_targ1 pd wt def))
  (I1: getinstr f v = Some (Iload chunk addr args dst)),
  v <> v_targ1 ->
  False.
Proof.
  intros.
  apply target_gives_tainted_ir_inner in INIT2 as [? []]; auto.
  apply UNI_MEM in I1. apply I1 in H1. auto. rewrite UNIFORM in H0. unfold TaintAnalysis.uniform_cond in H0. now rewrite negb_false_iff in H0.
  clear INIT2. eapply postdom_before in pd; eauto. apply top_sort_g. split; intro; now apply EXIT.
Qed.

Lemma step_cond_cond:
  forall ifso1 ifso2 ifnot1 ifnot2 b1 b2 v v_targ w1 w2 c1 args1 c2 args2 rs1 rs2 m
  (I1: getinstr f v = Some (Icond c1 args1)) (I2: getinstr f v = Some (Icond c2 args2))
  (S1: successors f.(g_pred) v = ifso1 :: ifnot1 :: nil) (S2: successors f.(g_pred) v = ifso2 :: ifnot2 :: nil)
  (E1: eval_condition c1 rs1 ## args1 m = Some b1) (E2: eval_condition c2 rs2 ## args2 m = Some b2)
  (pd: postdom (g f) (exit f) v_targ v),
  agree_publicly rs1 rs2 ->
  w1 = f.(detour) v (if b1 then ifso1 else ifnot1) ->
  w2 = f.(detour) v (if b2 then ifso2 else ifnot2) ->
  w1 = w2 /\ agree_publicly rs1 rs2.
Proof.
  intros. case (uniform_cond f v) eqn:?.
  - enough (b1 = b2). { rewrite S1 in S2. injection S2. intros. now subst. }
    eapply uniform_cond_has_clean_params in Heqb; eauto.
    apply agree_on_public_list with (regs:=args2) in H; auto.
    rewrite <- H in E2. rewrite I1 in I2. injection I2. intros. subst. rewrite E1 in E2. now injection E2.
  - assert (vertex f.(g_pred) v). { apply vertex_same; destruct pd; now destruct H3. }
    apply f.(SUCCS_COND) in I1. apply I1 in Heqb. eapply tainted_cond_same_target in Heqb.
    now rewrite H0, H1, Heqb.
    case b1; apply successors_spec; auto; rewrite S1; [|apply in_cons]; apply in_eq.
    case b2; apply successors_spec; auto; rewrite S2; [|apply in_cons]; apply in_eq.
Qed.

Theorem cut_right: forall (A B C: Prop), (C -> B) -> A /\ C -> A /\ B.
Proof.
  intros. enow destruct H0.
Qed.

Lemma control_flow_security_single_step:
  forall init1 init2 tr1 tr2 sp sp1' sp2' v v1' v2' rs1 rs1' rs2 rs2' m v_target1 v_target1' v_target2 v_target2' pd1 pd2 pd1' pd2' wt1 wt2 wt1' wt2' def1 def2 def1' def2'
  (INIT1: initial_state tprog init1)
  (INIT2: initial_state tprog init2)
  (INIT3: star_tr init1 tr1 (State f sp v rs1 m v_target1 pd1 wt1 def1))
  (INIT4: star_tr init2 tr2 (State f sp v rs2 m v_target2 pd2 wt2 def2)),
  agree_publicly rs1 rs2 ->
  step tge (State f sp v rs1 m v_target1 pd1 wt1 def1) E0 (State f sp1' v1' rs1' m v_target1' pd1' wt1' def1') ->
  step tge (State f sp v rs2 m v_target2 pd2 wt2 def2) E0 (State f sp2' v2' rs2' m v_target2' pd2' wt2' def2') ->
  v1' = v2' /\ agree_publicly rs1' rs2'.
Proof.
  intros. pose proof H0 as H0copy.
  dependent destruction H0. (* somehow, inversion doesn't provide the fact that getinstr f v = Iop *)

  * (* do_nothing *)
  pose proof H1 as H1copy. dependent destruction H1. 
  + rewrite U0 in U. now injection U.
  + unfold uniquesucc in U. now rewrite S in U.
  + rewrite U0 in U. now injection U.
  + eapply step_nop_op. 6: apply OP. 6: apply N. 2: apply INIT3. all: eauto.
  + exfalso. enow eapply step_nop_load with (init:=init1).
  + unfold uniquesucc in U. now rewrite S in U.
  
  * (* do_nothing_cond *)
  dependent destruction H1. 
  + unfold uniquesucc in U. now rewrite S in U.
  + eapply step_cond_cond. 5: apply H0. 5: apply H1. 7: enow unfold w. all: eauto.
  + rewrite I in I0. congruence.
  + rewrite I in I0. congruence.
  + rewrite I in I0. congruence.
  + eapply step_cond_cond. 5: apply H0. 5: apply H1. 7: enow unfold w. all: eauto.

  * (* exec_Inop *)
  dependent destruction H1.
  + rewrite U0 in U. now injection U.
  + rewrite I in I0. congruence.
  + rewrite U0 in U. now injection U.
  + rewrite I in I0. congruence.
  + rewrite I in I0. congruence.
  + rewrite I in I0. congruence.

  * (* exec_Iop *)
  copy H1. dependent destruction H1.
  + eapply cut_right; [apply agree_publicly_sym|].
    eapply step_nop_op. 6: apply OP. all: eauto. now apply agree_publicly_sym.
  + rewrite I in I0. congruence.
  + rewrite I in I0. congruence.
  + rewrite U0 in U. injection U; intros. rewrite I0 in I. injection I; intros.
    subst. split; eauto.
    case (public_list_dec args) eqn:?.
    - erewrite agree_on_public_list in OP; eauto. rewrite OP0 in OP. injection OP; intros.
      subst. apply agree_publicly_assign_same; auto.
    - clear Heqs. replace args with (instr_uses (Iop op args res)) in n. eapply taint_ana_instr_uses in n; eauto.
      enow apply agree_publicly_assign_tainted. auto. auto.
  + rewrite I in I0. congruence.
  + rewrite I in I0. congruence.

  * (* exec_Iload *)
  copy H1. dependent destruction H1.
  + exfalso. enow eapply step_nop_load with (init:=init2).
  + rewrite I in I0. congruence.
  + rewrite I in I0. congruence.
  + rewrite I in I0. congruence.
  + rewrite U0 in U. injection U; intros. rewrite I0 in I. injection I; intros.
    subst. split; eauto.
    case (public_list_dec args) eqn:?.
    - erewrite agree_on_public_list in AD; eauto. rewrite AD0 in AD. injection AD; intros.
      rewrite <- H1, MEM0 in MEM. injection MEM; intro.
      subst. apply agree_publicly_assign_same; auto.
    - clear Heqs. replace args with (instr_uses (Iload chunk addr args dst)) in n. eapply taint_ana_instr_uses in n; eauto.
      enow apply agree_publicly_assign_tainted. auto. auto.
  + rewrite I in I0. congruence.

  * (* exec_Icond *)
  dependent destruction H1.
  + unfold uniquesucc in U. now rewrite S in U.
  + eapply step_cond_cond. 5: apply H0. 5: apply H1. 7: enow unfold w. all: eauto.
  + rewrite I in I0. congruence.
  + rewrite I in I0. congruence.
  + rewrite I in I0. congruence.
  + eapply step_cond_cond. 5: apply H0. 5: apply H1. 7: enow unfold w. all: eauto.
Qed.

Definition args_agree_publicly (args1 args2: list val) :=
  length args1 = length args2 /\
  forall i, i < length f.(params) -> In (nth i f.(params) xH) f.(taint_attr).(tainted_params) \/ nth i args1 Vundef = nth i args2 Vundef.

Definition init_states_agree_publicly (s1 s2: state) :=
  match s1, s2 with
  | InitState f1 args1 m1 wt1 def1, InitState f2 args2 m wt2 def2 => args_agree_publicly args1 args2
  | _, _ => False
  end.

Lemma init_rtl_agree_publicly: forall args1 args2,
  args_agree_publicly args1 args2 ->
  agree_publicly (RTL.init_regs args1 (params f)) (RTL.init_regs args2 (params f)).
Proof.
  unfold args_agree_publicly, agree_publicly. induction f.(params); intros. easy.
  destruct H. case args1 eqn:?, args2 eqn:?; [ easy | simpl in H; lia | simpl in H; lia | ].
  simpl. case (peq a r) eqn:?.
  * subst. rewrite Regmap.gss, Regmap.gss.
    assert (0 < length (r :: l)) by (simpl; lia). apply H1 in H2 as [].
    + assert (A: f.(taint_attr) = TaintAnalysis.taint_attr (taint_f f)) by auto.
      rewrite A in H2. eapply taint_ana_params_spec in H2; eauto.
      unfold public, tainted_reg in H0. simpl in H2. now rewrite H0 in H2.
    + easy.
  * rewrite Regmap.gso, Regmap.gso; try lia. apply IHl; auto. simpl in H. split. lia.
    intros. assert (S i < length (a::l)) by (simpl; lia). now apply H1 in H3.
Qed.

Lemma init_agree_publicly: forall args1 args2,
  args_agree_publicly args1 args2 ->
  agree_publicly (init_all_regs (env f) (code f) (params f) args1) (init_all_regs (env f) (code f) (params f) args2).
Proof.
  intros. unfold init_all_regs. induction (Pos.to_nat). now apply init_rtl_agree_publicly.
  simpl. match goal with [ H: agree_publicly ?i1 ?i2 |- _ ] => remember i1; remember i2 end.
  case (Val.eq Vundef (r @!! n)) eqn:?, (Val.eq Vundef (r0 @!! n)) eqn:?.
  * now apply agree_publicly_assign_same.
  * apply agree_publicly_sym, agree_publicly_assign_tainted'. now apply agree_publicly_sym.
    intro. clear Heqs0. rewrite e in n0. now apply n0, IHn.
  * apply agree_publicly_assign_tainted'. auto.
    intro. clear Heqs. rewrite e in n0. now apply n0, eq_sym, IHn.
  * auto.
Qed.

(* Main theorem: any two PredRTL executions of the same function with the same tainted parameters
   take the same path and modify public registers equivalently. *)
Theorem control_flow_security:
  forall init1 init2 sp v1 v2 trace1 trace2 rs1 rs2 m v_target1 v_target2 pd1 pd2 wt1 wt2 def1 def2
  (I1: initial_state tprog init1)
  (I2: initial_state tprog init2)
  (L: length trace1 = length trace2)
  (IA: init_states_agree_publicly init1 init2),
  star_tr init1 trace1 (State f sp v1 rs1 m v_target1 pd1 wt1 def1) ->
  star_tr init2 trace2 (State f sp v2 rs2 m v_target2 pd2 wt2 def2) ->
  trace1 = trace2 /\ v1 = v2 /\ agree_publicly rs1 rs2.
Proof.
  intros. generalize dependent v1. generalize dependent v2. dependent induction trace1.
  { case trace2 eqn:?; [|easy]. intros. inv H; [inv I1|congruence]. }
  assert (F: function init1 = function init2).
  { inv I1. inv I2. simpl. unfold ge, ge0 in *. rewrite H0 in H3. injection H3. intro. rewrite H5, H4 in H1. now injection H1. } 
  
  case trace2 eqn:?; [easy|]. intros. rename trace2 into trace2'. rename l into trace2.
  inv H. inv H0. simpl in *.
  injection H3. injection H5. intros.
  case s2 in *, s0 in *.
  3: inv H4. 5: inv H4. 5: inv H2. 5: inv H2. 5: inv H4. (* EndStates *)
  
  (* Two InitStates *)
  4: {
    inv H1; [|inv H10]. inv H; [|inv H1]. simpl in F. subst f0.
    inv H2. inv H4. intros. subst. do 2 split; auto.
    simpl in IA. now apply init_agree_publicly.
  }
  (* Invalid: InitState & normal state *)
  2: { inv H; [|inv H10]. inv H1; [inv I1|]. intros. subst. simpl in L. lia. }
  2: { inv H1; [|inv H10]. inv H; [inv I2|]. intros. subst. simpl in L. lia. }

  (* Normal case: two states *)
  injection L. intro T.
  assert (f1 = f) by now inv H4. assert (f0 = f) by now inv H2. subst f1 f0.
  assert (sp1 = sp) by now inv H4. assert (sp0 = sp) by now inv H2. subst sp1 sp0.
  assert (m1 = m) by now inv H4. assert (m0 = m) by now inv H2. subst m1 m0.
  assert (tr3 = E0) by now inv H4. assert (tr2 = E0) by now inv H2.
  eapply IHtrace1 in T as [? []]. 5: { rewrite H0. apply H. } 5: { rewrite H7. apply H1. }
  all: eauto. subst v0.
  eapply control_flow_security_single_step in H13. 4: apply H1. 4: apply H. 4: { rewrite <- H10. apply H2. } 4: { rewrite <- H9. apply H4. }
  all: eauto.
  subst. destruct H13. split; auto.
Qed.

End Security.