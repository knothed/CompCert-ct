
Require Import Coqlib Integers List Maps.
Require Import Registers Globalenvs Values Op.
Require Import Common SafeOp SharedTypes.

(* Show that safe operations return safe (i.e. non-undef) values when given safe arguments. *)

Section Icond.

Lemma execute_Icond:
  forall fd (ge: Genv.t fd unit) env sig max cond args rs m,
  condition_safe cond ->
  (forall r, In r args -> Ple r max) ->
  wt_instr env sig (Icond cond args) ->
  wt_regset env rs ->
  def_regset max rs ->
  exists v, eval_condition cond rs##args m = Some v.
Proof.
  intros until m. intros SAFE MAX WTIN WTREG DEF.
  destruct cond.
  Local Transparent Archi.ptr64.

  Ltac simpl_env env := match goal with
    | [ H : map env ?a = ?b |- _ ] => simpl in H; try congruence; injection H; intros
    | [ H : env ?p :: ?q = ?r |- _ ] => simpl in H; try congruence; injection H; intros
  end.
  Ltac simpl_args := match goal with [ WTIN: wt_instr ?env _ _ |- exists _, eval_condition _ ?rs##?args _ = Some _ ] =>
    simpl; inv WTIN; repeat (destruct args; try simpl_env env; try congruence)
  end.
  
  Ltac unfold_single_wt env H p := match goal with [ WTREG: wt_regset env _ |- _ ] =>
    let WTP := fresh in pose proof (WTREG p) as WTP; rewrite H in WTP
  end.
  Ltac unfold_single_def env H p := match goal with [ DEF: def_regset _ _, MAX: forall _, In _ _ -> Ple _ ?max |- _ ] =>
    clear H; let PLE := fresh "P" in assert (PLE: Ple p max) by (apply MAX; repeat (apply in_eq || apply in_cons)); apply DEF in PLE
  end.
  Ltac unfold_all_wt_def env := repeat match goal with [ H: env ?p = _ |- _ ] => unfold_single_wt env H p; unfold_single_def env H p; clear H end.
  
  Ltac elim_match := match goal with [ |- exists _, match (?rs !! ?p) with _ => _ end = _ ] =>
    let R := fresh in case (rs !! p) eqn:R; simpl in *; unfold Archi.ptr64 in *; try elim_match; try now exfalso; congruence
  end.

  Ltac elim_match' rs r :=
    let R := fresh in case (rs !! r) eqn:R; simpl in *; unfold Archi.ptr64 in *; try elim_match; try now exfalso; congruence.

  Ltac unfold_op := simpl; match goal with
    | [ |- exists _, ?op _ _ = _ ] => unfold op
    | [ |- exists _, ?op _ _ _ = _ ] => unfold op
    | [ |- exists _, ?op _ _ _ _ = _ ] => unfold op
  end.

  all: try inv SAFE.
  all: simpl_args; unfold_op; unfold_all_wt_def env;
       try elim_match; try elim_match' rs p; try elim_match' rs p0;
       enow eexists.
Qed.

End Icond.

Section Iop.

Lemma max_foldl_start: forall l d e, Ple d e -> Ple d (fold_left Pos.max l e).
Proof.
  induction l. simpl; extlia.
  intros. destruct (peq e a); apply IHl; extlia.
Qed.

Lemma max_foldl_in: forall p l d, In p l -> Ple p (fold_left Pos.max l d).
Proof.
  intros. induction l. contradiction.
  destruct H.
  * subst. simpl. apply max_foldl_start. extlia.
  * apply IHl in H. rewrite fold_symmetric. simpl. rewrite <- fold_symmetric. all: extlia.
Qed.

Lemma def_exec_Iop:
  forall fd (ge: Genv.t fd unit) env sig max sp op args res rs m v
  (SP: exists b ofs, sp = Vptr b ofs),
  op_safe op ->
  eval_operation ge sp op rs##args m = Some v ->
  (forall r, In r args -> Ple r max) ->
  Ple res max ->
  wt_instr env sig (Iop op args res) ->
  wt_regset env rs ->
  def_regset max rs ->
  def_regset max (rs#res <- v).
Proof.
  intros until v. intros SP SAFE EVAL MAX MAX2 WTIN WTREG DEF. apply def_regset_assign; auto.
  destruct op.
  all: try (inv SAFE; fail).
  Local Transparent Archi.ptr64.

  Ltac simpl_args := match goal with [ EVAL: eval_operation _ _ _ ?rs##?args _ = Some _ |- _ ] =>
    simpl in EVAL; repeat (destruct args; simpl in EVAL; try congruence); (injection EVAL; let E := fresh in intro E; rewrite <- E)
  end.
  
  Ltac simpl_env env := match goal with
    | [ H : map env ?a = ?b |- _ ] => simpl in H; injection H; intros
    | [ H : env ?p :: ?q = ?r |- _ ] => simpl in H; injection H; intros
  end.
  Ltac unfold_single_wt env H p := match goal with [ WTREG: wt_regset env _ |- _ ] =>
    let WTP := fresh in pose proof (WTREG p) as WTP; rewrite H in WTP
  end.
  Ltac unfold_single_def env H p := match goal with [ DEF: def_regset _ _, MAX: forall _, In _ _ -> Ple _ ?max |- _ ] =>
    clear H; copy MAX; let PLE := fresh "P" in assert (PLE: Ple p max) by (apply MAX; repeat (apply in_eq || apply in_cons)); apply DEF in PLE
  end.
  Ltac unfold_all_wt_def env := match goal with [ WTIN: wt_instr env _ _ |- _ ] =>
    inv WTIN; simpl_env env;
    repeat match goal with [ H: env ?p = _ |- _ ] => unfold_single_wt env H p; unfold_single_def env H p; clear H end
  end.

  Ltac elim_match := match goal with [ |- match (?rs !! ?p) with _ => _ end <> Vundef ] =>
    let R := fresh in case (rs !! p) eqn:R; simpl in *; unfold Archi.ptr64 in *; try elim_match; congruence
  end.
  Ltac elim_match_rewriting H := match goal with [ |- match (?rs !! ?p) with _ => _ end <> Vundef ] =>
    let R := fresh in case (rs !! p) eqn:R; simpl in *; unfold Archi.ptr64 in *; try elim_match; try rewrite H; congruence
  end.

  Ltac unfold_op := match goal with
    | [ |- ?op _ <> Vundef ] => unfold op
    | [ |- ?op _ _ <> Vundef ] => unfold op
    | [ |- ?op _ _ _ <> Vundef ] => unfold op
  end.

  1-5: simpl_args; apply DEF; apply MAX; apply in_eq.
  1-17: simpl_args; unfold_op; unfold_all_wt_def env; elim_match.
  1-2: simpl_args; unfold_op; unfold_all_wt_def env; inv SAFE; elim_match_rewriting H1.
  1-3: simpl_args; unfold_op; unfold_all_wt_def env; inv SAFE; elim_match_rewriting H1.
  1-2: simpl_args; unfold_op; unfold_all_wt_def env; elim_match.
  2-17: simpl_args; unfold_op; unfold_all_wt_def env; elim_match.
  
  (* Oleal *)
  + case a eqn:?; inv SAFE.
  * simpl in EVAL. case (args) eqn:? in EVAL. simpl in EVAL. congruence. case l eqn:? in EVAL; [|simpl in EVAL; congruence]. injection EVAL. intro.
    rewrite <- H. inv WTIN. simpl_env env. unfold_single_wt env H p. unfold_single_def env H p.
    unfold Val.addl. case (rs !! p) eqn:?; try congruence; try inv H0. simpl. congruence.
  * simpl in EVAL. case args eqn:? in EVAL. unfold Val.offset_ptr in EVAL. simpl in EVAL.
    decompose [ex] SP. case sp eqn:?; congruence.
    simpl in EVAL. congruence.
  (* Ocmp *)
  + exploit execute_Icond; eauto. Unshelve. 3-4: auto.
  * case cond eqn:C; inv WTIN; now constructor.
  * intros [x]. simpl in EVAL. rewrite H in EVAL. injection EVAL; intro E. case x in E; rewrite <- E; easy.
  (* Osel *)
  + simpl in EVAL. unfold Val.select in EVAL.
    do 2 (destruct args; simpl in EVAL; try congruence). injection EVAL; intro H; rewrite <- H.
    exploit execute_Icond. Unshelve. 13: exact args. all: eauto.
  * intros. apply MAX. now repeat apply in_cons.
  * case c eqn:C; inv WTIN; simpl in H4 |- *; injection H4; now constructor.
  * intros [x EC]. rewrite EC. inv WTIN; simpl in H4; injection H4; intros.
    unfold_single_wt env H1 p. unfold_single_wt env H0 p0.
    assert (PLE: Ple p max). { assert (P: In p (p::p0::args)) by apply in_eq. now apply MAX. }
    assert (PLE1: Ple p0 max). { assert (P0: In p0 (p::p0::args)) by apply in_cons, in_eq. now apply MAX. }
    apply DEF in PLE. apply DEF in PLE1.
    unfold Val.normalize. case x.
    - case (rs !! p) eqn:P; simpl in H2; case t in *; unfold Archi.ptr64 in *; congruence.
    - case (rs !! p0) eqn:P; simpl in H6; case t in *; unfold Archi.ptr64 in *; congruence.
Qed.

Lemma execute_Iop:
  forall fd (ge: Genv.t fd unit) env sig sp op args res rs m,
  wt_instr env sig (Iop op args res) ->
  wt_regset env rs ->
  op_safe op ->
  exists v,
  eval_operation ge sp op rs##args m = Some v.
Proof.
  intros until m. intros WTIN WTREG SAFE. destruct op.
  all: try (inv SAFE; fail).
  Ltac simpl_env2 env := match goal with [ H : map env ?a = ?b |- _ ] => simpl in H | [ H : env ?p :: ?q = ?r |- _ ] => simpl in H end.
  Local Transparent Archi.ptr64.
  48: case c in *.
  47: case cond in *.
  30: case a in *.
  all: inv WTIN; try congruence; repeat (destruct args; simpl_env2 env; try congruence); try enow simpl.
Qed.

End Iop.