Require Import Axioms Common Coqlib Classical Datatypes.
Require Import AST Memory Registers Maps Values Events Globalenvs Smallstep Op Integers.
Require Import ControlFlowSecurity.
Require Import ListsExtra Graph GraphDual PredRTL SelRTL SharedTypes SafeOpProof.
Require Import Before.
Require Import PCFL PCFLBranchMapping PCFLEdgeEmbedding.
Require Import Smallstep Errors Linking.
Require Import Predication.
Require Import MemAxiom.

Definition regs_are_constant (f: PredRTL.function) (rs: regset): Prop :=
  forall (r: nat), r < f.(PredRTL.n) ->
  rs !! (Pos.of_succ_nat r + cond_which_reg f) = nat2val r.

Lemma regs_are_still_constant: forall f rs r v,
  Ple r (cond_which_reg f) ->
  regs_are_constant f rs ->
  regs_are_constant f (rs # r <- v).
Proof.
  intros. intro. intros.
  rewrite Regmap.gso; [now apply H0 | extlia].
Qed.

Lemma set_regs_are_constant: forall f rs,
  regs_are_constant f (set_regs_seq rs f.(PredRTL.n) (Pos.to_nat (cond_which_reg f))).
Proof.
  unfold regs_are_constant. intros.
  erewrite <- set_regs_seq_new. f_equal; eauto. extlia. auto.
Qed.

Inductive match_states: PredRTL.state -> SelRTL.state -> Prop :=
  | match_state:
      forall f tf sp v v_targ rs rs' m pd wt def wt'
        (TF: transl_function f = OK tf)
        (LD: regs_lessdef rs rs')
        (TARG: rs' # (targ_reg f) = nat2val v_targ)
        (CONST: regs_are_constant f rs'),
        match_states (PredRTL.State f sp v rs m v_targ pd wt def)
                     (SelRTL.State tf sp v rs' m wt')
  | match_initstate:
      forall args f tf m wt wt' def
        (TF: transl_fundef f = OK tf),
        match_states (PredRTL.InitState f args m wt def) (SelRTL.InitState tf args m wt' def)
  | match_endstate:
      forall f tf v v' m
        (TF: transl_fundef f = OK tf)
        (LD: Val.lessdef v v'),
        match_states (PredRTL.EndState f v m) (SelRTL.EndState tf v' m).

Definition match_prog (p: PredRTL.program) (tp: SelRTL.program) :=
  match_program (fun cu f tf => transl_fundef f = OK tf) eq p tp.

Lemma transf_program_match: forall p tp, transf_program p = OK tp -> match_prog p tp.
Proof.
  intros. now apply match_transform_partial_program.
Qed.


Section Preservation.

Variable prog: PredRTL.program.
Variable tprog: SelRTL.program.
Hypothesis TRANSL: match_prog prog tprog.

Let ge : PredRTL.genv := Genv.globalenv prog.
Let tge : SelRTL.genv := Genv.globalenv tprog.

(* Trivial boilerplate *)

Lemma symbols_preserved:
  forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
Proof (Genv.find_symbol_transf_partial TRANSL).

Lemma senv_preserved:
  Senv.equiv (Genv.to_senv ge) (Genv.to_senv tge).
Proof (Genv.senv_transf_partial TRANSL).

Lemma function_ptr_translated:
  forall (b: block) (f: PredRTL.fundef),
  Genv.find_funct_ptr ge b = Some f ->
  exists tf,
  Genv.find_funct_ptr tge b = Some tf /\ transl_fundef f = OK tf.
Proof (Genv.find_funct_ptr_transf_partial TRANSL).

Lemma sig_function_translated:
  forall f tf,
  transl_fundef f = OK tf ->
  SelRTL.funsig tf = PredRTL.funsig f.
Proof.
  intros. unfold SelRTL.funsig, PredRTL.funsig.
  unfold transl_fundef, transf_partial_fundef, bind, transl_function in H.
  destruct tf eqn:TF; destruct f eqn:F; try congruence.
  injection H; intro; now subst.
Qed.

(* Initial and final states *)

Lemma transl_initial_states:
  forall S, PredRTL.initial_state prog S ->
  exists R, SelRTL.initial_state tprog R /\ match_states S R.
Proof.
  intros. inv H.
  exploit function_ptr_translated. eauto.  intros [tf [G T]].
  eexists (SelRTL.InitState tf nil m0 _ _). split.
    econstructor.
  - now apply (Genv.init_mem_transf_partial TRANSL).
  - replace (prog_main tprog) with (prog_main prog). rewrite symbols_preserved. eauto.
    symmetry. eapply match_program_main. eauto.
  - apply G.
  - constructor.
  Unshelve. auto. rewrite <- FS. now apply sig_function_translated.
Qed.

Lemma transl_final_states:
  forall S R r,
  match_states S R -> PredRTL.final_state S r -> SelRTL.final_state R r.
Proof.
  intros. inv H0. inv H. inv LD. constructor.
Qed.

(* Step *)

Lemma unfold_transl: forall f tf,
  transl_function f = OK tf ->
  transl_code f = tf.(code) /\ transl_graph f = tf.(g).
Proof.
  unfold transl_function. intros. injection H. intro X. now rewrite <- X.
Qed.

Lemma unfold_env: forall f tf,
  transl_function f = OK tf ->
  new_env f = env tf.
Proof.
  unfold transl_function. intros. injection H. intro X. now rewrite <- X.
Qed.

Section Step7.

Variable f: PredRTL.function.
Variable tf: function.

Hypothesis TF: transl_function f = OK tf.
Hypothesis C: tf.(code) = transl_code f.
Hypothesis G: tf.(g) = transl_graph f.
Hypothesis E: tf.(env) = new_env f.

Variable v v_targ: nat.
Variable sp: val.
Variable m: mem.
Variable rs' rs: regset.

Variable VN: v < f.(PredRTL.n).
Variable VTN: v_targ < f.(PredRTL.n).
Variable TARG: rs !! (targ_reg f) = nat2val v_targ.
Variable CONST: regs_are_constant f rs.
Variable LESS: regs_lessdef rs' rs.
Let FS := f.(N_MAX).

Ltac solve_wt := match goal with
  | [ |- wt_regset (env tf) ?rs ] =>
    auto;
    apply wt_regset_assign; auto;
    try (rewrite E; (rewrite new_type_v_reg || rewrite new_type_targ_reg || rewrite new_type_targ_new_reg || rewrite new_type_livereg || rewrite new_type_cond_which_reg); simpl; constructor)
  end.

Ltac solve_regs_constant := match goal with
  [ |- regs_are_constant f (?rs # ?r <- ?v) ] =>
    apply regs_are_still_constant; [unfold_regs; extlia |];
    auto;
    try solve_regs_constant
  end.

Lemma const: forall r,
  r < f.(PredRTL.n) ->
  rs !! (const_reg f r) = nat2val r.
Proof.
  intros. unfold const_reg. now rewrite CONST.
Qed.

Lemma def_rev: forall r,
  PredRTL.def_regset f rs' ->
  Plt (max_reg_function f.(PredRTL.code) f.(PredRTL.params)) r ->
  rs' # r = Vundef.
Proof.
  intros. case (rs' !! r) eqn:?; auto;
  assert (rs' !! r <> Vundef) by congruence; apply H in H1; extlia.
Qed.


Ltac prepare I :=
  decompose [and] (new_code_spec_1 f v VN); decompose [and] (new_successors_1 f v VN);
  unfold PredRTL.getinstr in I;
  pose proof FS; pose proof VN; pose proof VTN;
  replace v with (set_v_pc v) by now unfold set_v_pc.

Ltac prepare_unique U :=
  let U0 := fresh "U0" in pose proof U as U0; eapply uniquesucc_edge_full in U as [?[]]; eauto;
  let SG := fresh "SG" in let SP := fresh "SP" in eapply uniquesucc_edge_succs_full in U0 as [SG SP]; eauto.

Ltac transfstep := match goal with
  | [ H: (transl_code f) @! (?pc) = Some (?instr _) |- getinstr tf (?pc) = Some ?i ] =>
    unfold getinstr; rewrite C, H; unfold instr; eauto
  | [ H: (transl_code f) @! (?pc) = Some (?instr _ _) |- getinstr tf (?pc) = Some ?i ] =>
    unfold getinstr; rewrite C, H; unfold instr; eauto
  | [ H: (transl_code f) @! (?pc) = Some (?instr _ _ _) |- getinstr tf (?pc) = Some ?i ] =>
    unfold getinstr; rewrite C, H; unfold instr; eauto
  | [ H: successors (transl_graph f) (?pc) = _ |- uniquesucc tf (?pc) = Some (?instr _ _) ] =>
    unfold uniquesucc; rewrite G, H; auto
  end.

Ltac do_gsso :=
  (rewrite Regmap.gss; try do_gsso) ||
  (rewrite Regmap.gso; [|unfold_regs; extlia]; try do_gsso).

Lemma dummy_nop: forall w w' wt def wt1 pd
  (I: PredRTL.getinstr f v = Some Inop)
  (U: PredRTL.uniquesucc f v = Some (w, w')),
  v <> v_targ ->
  exists rs_new wt',
    plus SelRTL.step tge (State tf sp v rs m wt1) E0 (State tf sp w rs_new m wt') /\
    match_states (PredRTL.State f sp w rs' m v_targ pd wt def) (State tf sp w rs_new m wt').
Proof.
  intros. prepare I. prepare_unique U.
  
  do 2 eexists. split.
    set (rs1 := rs # (v_reg f) <- (nat2val v)).
    econstructor 1 with (t1:=E0) (t2:=E0) (s2:=State tf sp (live_pc f v) rs1 m _).
      eapply exec_Iop. transfstep. transfstep. auto.
    set (rs2 := rs1 # (livereg f) <- Vfalse).
    econstructor 2 with (t1:=E0) (t2:=E0) (s2:=State tf sp (instr_1_pc f v) rs2 m  _).
      eapply exec_Iop. transfstep. auto. transfstep.
      simpl. unfold rs1. rewrite Regmap.gss, Regmap.gso; [|unfold_regs; lia]. rewrite TARG.
      simpl. rewrite nat2int_int_neq; auto; lia.
    econstructor 2 with (t1:=E0) (t2:=E0) (s2:=State tf sp (instr_2_pc f v) rs2 m _).
      apply exec_Inop. transfstep. now rewrite I. transfstep.
    econstructor 2 with (t1:=E0) (t2:=E0) (s2:=State tf sp (set_v_targ_new_pc f v) rs2 m _).
      apply exec_Inop. transfstep. now rewrite I. transfstep.
    set (rs3 := rs2 # (targ_new_reg f) <- (nat2val w')).
    econstructor 2 with (t1:=E0) (t2:=E0) (s2:=State tf sp (set_v_targ_pc f v) rs3 m _).
      eapply exec_Iop. transfstep. rewrite SG. eauto.
      transfstep. auto.
    set (rs4 := rs3 # (targ_reg f) <- (rs3 # (targ_reg f))).
    econstructor 2 with (t1:=E0) (t2:=E0) (s2:=State tf sp (closing_pc f v) rs4 m _).
      eapply exec_Isel. transfstep. transfstep.
        unfold rs3, rs2, eval_sel.
        rewrite Regmap.gss, Regmap.gso, Regmap.gss, Regmap.gso, Regmap.gso; try (unfold_regs; lia).
        apply Val.normalize_idem.
        unfold rs1. rewrite Regmap.gso; [|unfold_regs; lia]. now rewrite TARG.
    econstructor 2 with (t1:=E0) (t2:=E0) (s2:=State tf sp w rs4 m _).
      apply exec_Inop. transfstep. now rewrite I.
      unfold uniquesucc. now rewrite G, (new_successors_2 f v VN), SP.
    econstructor 1.
    all: eauto.

  econstructor. apply TF. unfold_regs. apply lessdef_new_four; auto; apply def_rev; auto; try extlia.
  rewrite Regmap.gss. repeat rewrite Regmap.gso; unfold_regs; try apply TARG. extlia.

  lia. lia.

  Unshelve.
  solve_regs_constant.
  all: repeat solve_wt.
  * unfold rs3, rs2, rs1; repeat rewrite Regmap.gso; try (unfold_regs; extlia); apply wt1.
Qed.


Lemma dummy_op: forall w w' wt def wt1 pd op args res opres
  (I: PredRTL.getinstr f v = Some (Iop op args res))
  (U: PredRTL.uniquesucc f v = Some (w, w'))
  (UNI: ~ uni f v),
  eval_operation ge sp op rs'##args m = Some opres ->
  v <> v_targ ->
  exists rs_new wt',
    plus SelRTL.step tge (State tf sp v rs m wt1) E0 (State tf sp w rs_new m wt') /\
    match_states (PredRTL.State f sp w rs' m v_targ pd wt def) (State tf sp w rs_new m wt').
Proof.
  intros. prepare I. prepare_unique U.
  assert (Ple res (max_reg_function f.(PredRTL.code) f.(PredRTL.params))) by enow eapply max_reg_function_def.

  (* for wt later *)
  assert (WTOP: Val.has_type opres (env tf (dummy_reg f res))).
  { rewrite E, new_type_dummy_reg; [|now unfold maxreg].
    destruct f.(PredRTL.WELLTYPED). apply wt_instrs in I. inv I.
    + simpl in H. injection H; intro X; rewrite <- X, H22. apply wt.
    + eapply type_of_operation_sound in H24; eauto. now rewrite H26. }

  do 2 eexists. split.
    set (rs1 := rs # (v_reg f) <- (nat2val v)).
    econstructor 1 with (t1:=E0) (t2:=E0) (s2:=State tf sp (live_pc f v) rs1 m _).
      eapply exec_Iop. transfstep. transfstep. auto.
    set (rs2 := rs1 # (livereg f) <- Vfalse).
    econstructor 2 with (t1:=E0) (t2:=E0) (s2:=State tf sp (instr_1_pc f v) rs2 m  _).
      eapply exec_Iop. transfstep. auto. transfstep.
      simpl. unfold rs1. rewrite Regmap.gss, Regmap.gso; [|unfold_regs; lia]. rewrite TARG.
      simpl. rewrite nat2int_int_neq; auto; lia.
    set (rs3 := rs2 # (dummy_reg f res) <- opres).
    econstructor 2 with (t1:=E0) (t2:=E0) (s2:=State tf sp (instr_2_pc f v) rs3 m _).
      eapply exec_Iop. transfstep. rewrite I. destruct uni_dec eqn:?; [ exfalso; clear Heqs; now apply UNI in u | ]. eauto.
      transfstep.
      erewrite eval_operation_preserved; [eauto | apply symbols_preserved]. erewrite <- regs_def_same with (rs1:=rs') (rs2:=rs2). eauto.
        apply lessdef_new_two; [apply LESS | |]; unfold_regs; apply def_rev; auto; extlia.
        eexact def.
        intros. eapply Ple_trans with (r:=max_reg_function _ _); [ now apply max_reg_instr_uses with (i:=Iop op args res) | enow eapply max_reg_instr_function ].
    set (rs4 := rs3 # res <- (rs3 # res)).
    econstructor 2 with (t1:=E0) (t2:=E0) (s2:=State tf sp (set_v_targ_new_pc f v) rs4 m _).
      eapply exec_Isel. transfstep. destruct uni_dec eqn:?; [ exfalso; clear Heqs; now apply UNI in u | ].
      now rewrite I. transfstep.
        unfold rs3, rs2, eval_sel.
        rewrite Regmap.gso, Regmap.gss, Regmap.gss, Regmap.gso, Regmap.gso; try (unfold_regs; extlia).
        apply Val.normalize_idem.
        unfold rs1. rewrite Regmap.gso; [|unfold_regs; extlia].
        rewrite <- new_env_spec_1, <- E. apply wt1.
        unfold maxreg. eapply max_reg_function_def. apply I. auto.
    set (rs5 := rs4 # (targ_new_reg f) <- (nat2val w')).
    econstructor 2 with (t1:=E0) (t2:=E0) (s2:=State tf sp (set_v_targ_pc f v) rs5 m _).
      eapply exec_Iop. transfstep. rewrite SG. eauto.
      transfstep. auto.
    set (rs6 := rs5 # (targ_reg f) <- (rs5 # (targ_reg f))).
    econstructor 2 with (t1:=E0) (t2:=E0) (s2:=State tf sp (closing_pc f v) rs6 m _).
      eapply exec_Isel. transfstep. transfstep.
        enough (rs5 !! (livereg f) = Vfalse). unfold eval_sel. rewrite H21.
        unfold Val.maskzero_bool, Coqlib.option_map, Vtrue. simpl.
        apply Val.normalize_idem.
        unfold rs5, rs4, rs3, rs2, rs1.
        rewrite Regmap.gso, Regmap.gso, Regmap.gso, Regmap.gso, Regmap.gso; try (unfold_regs; extlia). now rewrite TARG.
        unfold rs5, rs4, rs3, rs2.
        rewrite Regmap.gso, Regmap.gso, Regmap.gso, Regmap.gss; try (unfold_regs; extlia). auto.
    econstructor 2 with (t1:=E0) (t2:=E0) (s2:=State tf sp w rs6 m _).
      apply exec_Inop. transfstep. now rewrite I.
      unfold uniquesucc. now rewrite G, (new_successors_2 f v VN), SP.
    econstructor 1.
    all: eauto.

    econstructor. apply TF. unfold_regs. apply lessdef_new_special_six_four_nop; auto; try apply def_rev; auto; extlia.
    rewrite Regmap.gss. repeat rewrite Regmap.gso; unfold_regs; try apply TARG; extlia.
    
  Unshelve.
  solve_regs_constant.
  all: repeat solve_wt.
  all: try unfold rs5, rs4; unfold rs3, rs2, rs1; repeat (rewrite Regmap.gso; [|unfold_regs; extlia]); apply wt1.
Qed.

Lemma dummy_cond: forall ifso ifnot (b: bool) w' cond args wt def wt1 pd
  (I: PredRTL.getinstr f v = Some (Icond cond args))
  (S: successors f.(g_pred) v = ifso::ifnot::nil)
  (B: w' = (if b then ifso else ifnot)),
  let w := f.(detour) v w' in
  eval_condition cond rs##args m = Some b ->
  v <> v_targ ->
  exists rs_new wt',
    plus SelRTL.step tge (State tf sp v rs m wt1) E0 (State tf sp w rs_new m wt') /\
    match_states (PredRTL.State f sp w rs' m v_targ pd wt def) (State tf sp w rs_new m wt').
Proof.
  intros. prepare I.
  
  do 2 eexists. split.
    set (rs1 := rs # (v_reg f) <- (nat2val v)).
    econstructor 1 with (t1:=E0) (t2:=E0) (s2:=State tf sp (live_pc f v) rs1 m _).
      eapply exec_Iop. transfstep. transfstep. auto.
    set (rs2 := rs1 # (livereg f) <- Vfalse).
    econstructor 2 with (t1:=E0) (t2:=E0) (s2:=State tf sp (instr_1_pc f v) rs2 m  _).
      eapply exec_Iop. transfstep. auto. transfstep.
      simpl. unfold rs1. rewrite Regmap.gss, Regmap.gso; [|unfold_regs; lia]. rewrite TARG.
      simpl. rewrite nat2int_int_neq; auto; lia.
    set (rs3 := rs2 # (cond_which_reg f) <- (if b then Vtrue else Vfalse)).
    econstructor 2 with (t1:=E0) (t2:=E0) (s2:=State tf sp (instr_2_pc f v) rs3 m _).
      eapply exec_Iop. transfstep. now rewrite I. transfstep.
        simpl. erewrite same_regvalues with (rs2:=rs) (max:=maxreg f); eauto. now rewrite H.
        intros. unfold rs2, rs1. repeat rewrite Regmap.gso; unfold_all_regs; auto; extlia.
        unfold_regs. intros. eapply max_reg_function_use with (params:=f.(PredRTL.params)) in I; [|enow simpl]; extlia.
    econstructor 2 with (t1:=E0) (t2:=E0) (s2:=State tf sp (set_v_targ_new_pc f v) rs3 m _).
      apply exec_Inop. transfstep. now rewrite I. transfstep.
    set (rs4 := rs3 # (targ_new_reg f) <- (nat2val w')).
    econstructor 2 with (t1:=E0) (t2:=E0) (s2:=State tf sp (set_v_targ_pc f v) rs4 m _).
      eapply exec_Isel. transfstep. rewrite S. eauto. transfstep.
        unfold rs3, rs2, rs1, eval_sel.
        repeat rewrite Regmap.gss. repeat rewrite Regmap.gso; try (unfold_regs; extlia).
        rewrite const. rewrite const.
        unfold Val.maskzero_bool, Coqlib.option_map, Vtrue, Vfalse.
        case b in *; rewrite B; apply Val.normalize_idem; unfold nat2val; constructor.
          { apply vertex_n, vertex_same, successors_spec with (v:=v); [ now apply vertex_same, vertex_n | rewrite S ]. now apply in_cons, in_eq. }
          { apply vertex_n, vertex_same, successors_spec with (v:=v); [ now apply vertex_same, vertex_n | rewrite S ]. now apply in_eq. }
    set (rs5 := rs4 # (targ_reg f) <- (rs3 # (targ_reg f))).
    econstructor 2 with (t1:=E0) (t2:=E0) (s2:=State tf sp (closing_pc f v) rs5 m _).
      eapply exec_Isel. transfstep. transfstep.
        unfold rs4, rs3, rs2, eval_sel.
        rewrite Regmap.gso, Regmap.gso, Regmap.gss; try (unfold_regs; extlia).
        rewrite Regmap.gso with (j:=targ_new_reg f) (i:=targ_reg f); [|unfold_regs; extlia].
        rewrite Regmap.gss, Regmap.gso, Regmap.gso; try (unfold_regs; extlia).
        apply Val.normalize_idem. unfold rs1. rewrite Regmap.gso; [|unfold_regs; extlia]. now rewrite TARG.
    econstructor 2 with (t1:=E0) (t2:=E0) (s2:=State tf sp w rs5 m _).
    case (f.(uniform_cond) v) eqn:?.
      (* uniform *)
      copy I. copy I. apply cond_num_successors in I. rewrite Heqb0 in I.
      case (successors f.(PredRTL.g) v) eqn:?; try case l eqn:?; try case l0 eqn:?; try (simpl in I; lia).
      eapply exec_Icond. transfstep. now rewrite I0, Heqb0.
      rewrite G, (new_successors_2 f v VN). exact Heql.
      simpl. unfold rs5, rs4, rs3. rewrite Regmap.gso, Regmap.gso, Regmap.gss; try (unfold_regs; extlia).
      Unshelve. 20: exact b. now case b.
      unfold w. rewrite B. apply DETOUR_COND_UNIFORM in I1; auto. rewrite Heql, S in I1. simpl in I1. injection I1. now case b.
      (* tainted *)
      copy I. copy I. apply cond_num_successors in I. rewrite Heqb0 in I.
      case (successors f.(PredRTL.g) v) eqn:?; try case l eqn:?; try (simpl in I; lia).
      eapply exec_Inop. transfstep. now rewrite I0, Heqb0.
      unfold uniquesucc. rewrite G, (new_successors_2 f v VN), Heql. 
      assert (VW: v → w' in f.(g_pred)). { apply successors_spec. enow eapply vertex_same, PredRTL.getinstr_vertex. rewrite B, S. case b; [|apply in_cons]; apply in_eq. }
      apply DETOUR_SPEC in VW as []. apply successors_spec in H17; [| enow eapply PredRTL.getinstr_vertex]. rewrite Heql in H17. unfold w. f_equal. now case H17.
    econstructor 1.
    all: eauto.

  econstructor. apply TF. unfold_regs. apply lessdef_new_five; auto; apply def_rev; auto; try extlia.
  rewrite Regmap.gss. repeat rewrite Regmap.gso; unfold_regs; try apply TARG; extlia.

  Unshelve.
  solve_regs_constant.
  all: repeat solve_wt.
  1-3: rewrite E, new_type_cond_which_reg; now case b.
  * unfold rs3, rs2, rs1; repeat rewrite Regmap.gso; try (unfold_regs; extlia); apply wt1.
Qed.

Lemma real_nop: forall w w' wt def wt1 pd
  (I: PredRTL.getinstr f v = Some Inop)
  (U: PredRTL.uniquesucc f v = Some (w, w')),
  v = v_targ ->
  exists rs_new wt',
    plus SelRTL.step tge (State tf sp v rs m wt1) E0 (State tf sp w rs_new m wt') /\
    match_states (PredRTL.State f sp w rs' m w' pd wt def) (State tf sp w rs_new m wt').
Proof.
  intros. prepare I. prepare_unique U. rewrite <- H in TARG.
  
  do 2 eexists. split.
    set (rs1 := rs # (v_reg f) <- (nat2val v)).
    econstructor 1 with (t1:=E0) (t2:=E0) (s2:=State tf sp (live_pc f v) rs1 m _).
      eapply exec_Iop. transfstep. transfstep. auto.
    set (rs2 := rs1 # (livereg f) <- Vtrue).
    econstructor 2 with (t1:=E0) (t2:=E0) (s2:=State tf sp (instr_1_pc f v) rs2 m  _).
      eapply exec_Iop. transfstep. auto. transfstep.
      simpl. unfold rs1. rewrite Regmap.gss, Regmap.gso; [|unfold_regs; lia]. rewrite TARG.
      simpl. rewrite nat2int_int_eq; auto; lia.
    econstructor 2 with (t1:=E0) (t2:=E0) (s2:=State tf sp (instr_2_pc f v) rs2 m _).
      apply exec_Inop. transfstep. now rewrite I. transfstep.
    econstructor 2 with (t1:=E0) (t2:=E0) (s2:=State tf sp (set_v_targ_new_pc f v) rs2 m _).
      apply exec_Inop. transfstep. now rewrite I. transfstep.
    set (rs3 := rs2 # (targ_new_reg f) <- (nat2val w')).
    econstructor 2 with (t1:=E0) (t2:=E0) (s2:=State tf sp (set_v_targ_pc f v) rs3 m _).
      eapply exec_Iop. transfstep. rewrite SG. eauto.
      transfstep. now simpl.
    set (rs4 := rs3 # (targ_reg f) <- (rs3 # (targ_new_reg f))).
    econstructor 2 with (t1:=E0) (t2:=E0) (s2:=State tf sp (closing_pc f v) rs4 m _).
      eapply exec_Isel. transfstep. transfstep.
        unfold eval_sel.
        replace (rs3 !! (livereg f)) with Vtrue by (unfold rs3, rs2; now rewrite Regmap.gso, Regmap.gss; [|unfold_regs; lia]).
        unfold Vtrue. apply Val.normalize_idem.
        unfold rs3. rewrite Regmap.gss. now unfold nat2val.
    econstructor 2 with (t1:=E0) (t2:=E0) (s2:=State tf sp w rs4 m _).
      apply exec_Inop. transfstep. now rewrite I.
      unfold uniquesucc. now rewrite G, (new_successors_2 f v VN), SP.
    econstructor 1.
    all: eauto.

  econstructor. apply TF. unfold_regs. apply lessdef_new_four; auto; apply def_rev; auto; extlia.
  now rewrite Regmap.gss, Regmap.gss.

  Unshelve.
  solve_regs_constant.
  all: repeat solve_wt.
  * unfold rs3. rewrite Regmap.gss, E, new_type_targ_reg. constructor.
Qed.

Lemma real_op: forall w w' pd op args res opres wt def wt1 (def2: PredRTL.def_regset f rs')
  (I: PredRTL.getinstr f v = Some (Iop op args res))
  (U: PredRTL.uniquesucc f v = Some (w, w')),
  eval_operation ge sp op rs'##args m = Some opres ->
  v = v_targ ->
  exists rs_new wt',
    plus SelRTL.step tge (State tf sp v rs m wt1) E0 (State tf sp w rs_new m wt') /\
    match_states (PredRTL.State f sp w (rs'#res<-opres) m w' pd wt def) (State tf sp w rs_new m wt').
Proof.
  intros. prepare I. prepare_unique U. rewrite <- H0 in TARG.
  assert (Ple res (max_reg_function f.(PredRTL.code) f.(PredRTL.params))) by enow eapply max_reg_function_def.
  
  (* for wt later *)
  assert (WTOP: Val.has_type opres (env tf res)).
  { rewrite E, new_type_normal_reg; [|now unfold maxreg].
    destruct f.(PredRTL.WELLTYPED). apply wt_instrs in I. inv I.
    + simpl in H. injection H; intro X. rewrite <- X, H22. enough (R: (rs' !! r1) = (rs' # res <- opres) !! r1) by (rewrite R; apply wt).
      now case (peq r1 res) eqn:?; [ rewrite X, e, Regmap.gss | rewrite Regmap.gso ].
    + eapply type_of_operation_sound in H24; eauto. now rewrite H26. }

  destruct (uni_dec f v) eqn:UNI.
  + (* uni *)
  do 2 eexists. split.
    set (rs1 := rs # (v_reg f) <- (nat2val v)).
    econstructor 1 with (t1:=E0) (t2:=E0) (s2:=State tf sp (live_pc f v) rs1 m _).
      eapply exec_Iop. transfstep. transfstep. auto.
    set (rs2 := rs1 # (livereg f) <- Vtrue).
    econstructor 2 with (t1:=E0) (t2:=E0) (s2:=State tf sp (instr_1_pc f v) rs2 m _).
      eapply exec_Iop. transfstep. auto. transfstep.
      simpl. unfold rs1. rewrite Regmap.gss, Regmap.gso; [|unfold_regs; lia]. rewrite TARG.
      simpl. rewrite nat2int_int_eq; auto; lia.
    set (rs3 := rs2 # res <- opres).
    econstructor 2 with (t1:=E0) (t2:=E0) (s2:=State tf sp (instr_2_pc f v) rs3 m _).
      eapply exec_Iop. transfstep. now rewrite I, UNI. transfstep.
      erewrite eval_operation_preserved; [eauto | apply symbols_preserved]. erewrite <- regs_def_same with (rs1:=rs') (rs2:=rs2). eauto.
        apply lessdef_new_two; [apply LESS | |]; unfold_regs; apply def_rev; auto; extlia.
        eexact def2.
        intros. eapply Ple_trans with (r:=max_reg_function _ _); [ now apply max_reg_instr_uses with (i:=Iop op args res) | enow eapply max_reg_instr_function ].
    econstructor 2 with (t1:=E0) (t2:=E0) (s2:=State tf sp (set_v_targ_new_pc f v) rs3 m _).
      apply exec_Inop. transfstep. now rewrite I, UNI. transfstep.
    set (rs4 := rs3 # (targ_new_reg f) <- (nat2val w')).
    econstructor 2 with (t1:=E0) (t2:=E0) (s2:=State tf sp (set_v_targ_pc f v) rs4 m _).
      eapply exec_Iop. transfstep. rewrite SG. eauto.
      transfstep. auto.
    set (rs5 := rs4 # (targ_reg f) <- (rs4 # (targ_new_reg f))).
    econstructor 2 with (t1:=E0) (t2:=E0) (s2:=State tf sp (closing_pc f v) rs5 m _).
      eapply exec_Isel. transfstep. transfstep.
        unfold rs4, rs3, rs2, eval_sel.
        rewrite Regmap.gso, Regmap.gso, Regmap.gss, Regmap.gss; try (unfold_regs; extlia).
        apply Val.normalize_idem.
        now unfold nat2val.
    econstructor 2 with (t1:=E0) (t2:=E0) (s2:=State tf sp w rs5 m _).
      apply exec_Inop. transfstep. now rewrite I.
      unfold uniquesucc. now rewrite G, (new_successors_2 f v VN), SP.
    econstructor 1.
    all: eauto.

    eapply max_reg_function_def with (params:=(PredRTL.params f)) in I; eauto. 2: enow simpl.
    econstructor. apply TF. unfold_regs. apply lessdef_new_special_five_four_op; auto; try apply def_rev; auto; extlia.
    now repeat rewrite Regmap.gss.
    
    solve_regs_constant.
    all: repeat solve_wt.

  + (* non-uni *)
  do 2 eexists. split.
    set (rs1 := rs # (v_reg f) <- (nat2val v)).
    econstructor 1 with (t1:=E0) (t2:=E0) (s2:=State tf sp (live_pc f v) rs1 m _).
      eapply exec_Iop. transfstep. transfstep. auto.
    set (rs2 := rs1 # (livereg f) <- Vtrue).
    econstructor 2 with (t1:=E0) (t2:=E0) (s2:=State tf sp (instr_1_pc f v) rs2 m _).
      eapply exec_Iop. transfstep. auto. transfstep.
      simpl. unfold rs1. rewrite Regmap.gss, Regmap.gso; [|unfold_regs; lia]. rewrite TARG.
      simpl. rewrite nat2int_int_eq; auto; lia.
    set (rs3 := rs2 # (dummy_reg f res) <- opres).
    econstructor 2 with (t1:=E0) (t2:=E0) (s2:=State tf sp (instr_2_pc f v) rs3 m _).
      eapply exec_Iop. transfstep. now rewrite I, UNI. transfstep.
      erewrite eval_operation_preserved; [eauto | apply symbols_preserved]. erewrite <- regs_def_same with (rs1:=rs') (rs2:=rs2). eauto.
        apply lessdef_new_two; [apply LESS | |]; unfold_regs; apply def_rev; auto; extlia.
        eexact def2.
        intros. eapply Ple_trans with (r:=max_reg_function _ _); [ now apply max_reg_instr_uses with (i:=Iop op args res) | enow eapply max_reg_instr_function ].
    set (rs4 := rs3 # res <- (rs3 # (dummy_reg f res))).
    econstructor 2 with (t1:=E0) (t2:=E0) (s2:=State tf sp (set_v_targ_new_pc f v) rs4 m _).
      eapply exec_Isel. transfstep. now rewrite I, UNI. transfstep.
      unfold rs3, rs2, eval_sel.
        rewrite Regmap.gso, Regmap.gss; [| unfold_regs; extlia ].
        apply Val.normalize_idem.
        rewrite Regmap.gss.
        pose proof (wt res). now rewrite Regmap.gss in H21.
    set (rs5 := rs4 # (targ_new_reg f) <- (nat2val w')).
    econstructor 2 with (t1:=E0) (t2:=E0) (s2:=State tf sp (set_v_targ_pc f v) rs5 m _).
      eapply exec_Iop. transfstep. rewrite SG. eauto.
      transfstep. auto.
    set (rs6 := rs5 # (targ_reg f) <- (rs5 # (targ_new_reg f))).
    econstructor 2 with (t1:=E0) (t2:=E0) (s2:=State tf sp (closing_pc f v) rs6 m _).
      eapply exec_Isel. transfstep. transfstep.
        unfold rs5, rs4, rs3, rs2, eval_sel.
        rewrite Regmap.gso, Regmap.gso, Regmap.gso, Regmap.gss, Regmap.gss; try (unfold_regs; extlia).
        apply Val.normalize_idem.
        now unfold nat2val.
    econstructor 2 with (t1:=E0) (t2:=E0) (s2:=State tf sp w rs6 m _).
      apply exec_Inop. transfstep. now rewrite I.
      unfold uniquesucc. now rewrite G, (new_successors_2 f v VN), SP.
    econstructor 1.
    all: eauto.

    econstructor. apply TF. unfold_regs. apply lessdef_new_special_six_four_op; auto; try apply def_rev; auto; extlia.
    now repeat rewrite Regmap.gss.

  Unshelve.
  solve_regs_constant.
  all: repeat solve_wt.
  all: try (rewrite E, new_type_dummy_reg, <- new_type_normal_reg, <- E; auto; now unfold maxreg).
  all: try (now unfold rs3; rewrite Regmap.gss).
  * unfold rs4. rewrite Regmap.gss, E, new_type_targ_reg. constructor.
  * unfold rs5. rewrite Regmap.gss, E, new_type_targ_reg. constructor.
Qed.

Lemma real_load: forall w w' pd chunk addr args dst a val wt def wt1 (def2: PredRTL.def_regset f rs')
  (I: PredRTL.getinstr f v = Some (Iload chunk addr args dst))
  (U: PredRTL.uniquesucc f v = Some (w, w'))
  (AD: eval_addressing ge sp addr rs'##args = Some a)
  (MEM: Mem.loadv chunk m a = Some val),
  v = v_targ ->
  exists rs_new wt',
    plus SelRTL.step tge (State tf sp v rs m wt1) E0 (State tf sp w rs_new m wt') /\
    match_states (PredRTL.State f sp w (rs'#dst<-val) m w' pd wt def) (State tf sp w rs_new m wt').
Proof.
  intros. prepare I. prepare_unique U. rewrite <- H in TARG.
  assert (Ple dst (max_reg_function f.(PredRTL.code) f.(PredRTL.params))) by enow eapply max_reg_function_def.

  do 2 eexists. split.
    set (rs1 := rs # (v_reg f) <- (nat2val v)).
    econstructor 1 with (t1:=E0) (t2:=E0) (s2:=State tf sp (live_pc f v) rs1 m _).
      eapply exec_Iop. transfstep. transfstep. auto.
    set (rs2 := rs1 # (livereg f) <- Vtrue).
    econstructor 2 with (t1:=E0) (t2:=E0) (s2:=State tf sp (instr_1_pc f v) rs2 m _).
      eapply exec_Iop. transfstep. auto. transfstep.
      simpl. unfold rs1. rewrite Regmap.gss, Regmap.gso; [|unfold_regs; lia]. rewrite TARG.
      simpl. rewrite nat2int_int_eq; auto; lia.
    set (rs3 := rs2 # dst <- val).
    econstructor 2 with (t1:=E0) (t2:=E0) (s2:=State tf sp (instr_2_pc f v) rs3 m _).
      apply eval_addressing_lessdef with (vl2:=rs2 ## args) in AD as [a' [AD]].
      erewrite eval_addressing_preserved in AD; [| symmetry; apply symbols_preserved].
      copy MEM. apply mem_load_always_defined in MEM0.
      eapply Mem.loadv_extends with (addr2:=a') in MEM as [val' [MEM]]; [| apply Mem.extends_refl | auto].
      assert (val = val') by (case val eqn:?; try congruence; now inv H21).
      eapply exec_Iload; eauto. transfstep. now rewrite I. transfstep. now subst.
      apply regs_lessdef_regs, lessdef_new_two; [apply LESS | |]; unfold_regs; apply def_rev; auto; extlia.
    econstructor 2 with (t1:=E0) (t2:=E0) (s2:=State tf sp (set_v_targ_new_pc f v) rs3 m _).
      apply exec_Inop. transfstep. now rewrite I. transfstep.
    set (rs4 := rs3 # (targ_new_reg f) <- (nat2val w')).
    econstructor 2 with (t1:=E0) (t2:=E0) (s2:=State tf sp (set_v_targ_pc f v) rs4 m _).
      eapply exec_Iop. transfstep. rewrite SG. eauto.
      transfstep. auto.
    set (rs5 := rs4 # (targ_reg f) <- (rs4 # (targ_new_reg f))).
    econstructor 2 with (t1:=E0) (t2:=E0) (s2:=State tf sp (closing_pc f v) rs5 m _).
      eapply exec_Isel. transfstep. transfstep.
        unfold rs4, rs3, rs2, eval_sel.
        rewrite Regmap.gso, Regmap.gso, Regmap.gss, Regmap.gss; try (unfold_regs; extlia).
        apply Val.normalize_idem.
        now unfold nat2val.
    econstructor 2 with (t1:=E0) (t2:=E0) (s2:=State tf sp w rs5 m _).
      apply exec_Inop. transfstep. now rewrite I.
      unfold uniquesucc. now rewrite G, (new_successors_2 f v VN), SP.
    econstructor 1.
    all: eauto.

  eapply max_reg_function_def with (params:=(PredRTL.params f)) in I; eauto. 2: enow simpl.
  econstructor. apply TF. unfold_regs. apply lessdef_new_special_five_four_op; auto; try apply def_rev; auto; extlia.
  now repeat rewrite Regmap.gss.
  
  Unshelve.
  solve_regs_constant.
  all: repeat solve_wt.
  1-3: rewrite E, new_type_normal_reg; auto; erewrite <- Regmap.gss with (x:=val); apply wt.
  * unfold rs4. rewrite Regmap.gss, E, new_type_targ_reg. constructor.
Qed.

Lemma real_cond: forall ifso ifnot (b: bool) w' cond args wt def wt1 pd
  (I: PredRTL.getinstr f v = Some (Icond cond args))
  (S: successors f.(g_pred) v = ifso::ifnot::nil)
  (B: w' = (if b then ifso else ifnot)),
  let w := f.(detour) v w' in
  eval_condition cond rs##args m = Some b ->
  v = v_targ ->
  exists rs_new wt',
    plus SelRTL.step tge (State tf sp v rs m wt1) E0 (State tf sp w rs_new m wt') /\
    match_states (PredRTL.State f sp w rs' m w' pd wt def) (State tf sp w rs_new m wt').
Proof.
  intros. prepare I. rewrite <- H0 in TARG.
  
  do 2 eexists. split.
    set (rs1 := rs # (v_reg f) <- (nat2val v)).
    econstructor 1 with (t1:=E0) (t2:=E0) (s2:=State tf sp (live_pc f v) rs1 m _).
      eapply exec_Iop. transfstep. transfstep. auto.
    set (rs2 := rs1 # (livereg f) <- Vtrue).
    econstructor 2 with (t1:=E0) (t2:=E0) (s2:=State tf sp (instr_1_pc f v) rs2 m _).
      eapply exec_Iop. transfstep. auto. transfstep.
      simpl. unfold rs1. rewrite Regmap.gss, Regmap.gso; [|unfold_regs; lia]. rewrite TARG.
      simpl. rewrite nat2int_int_eq; auto; lia.
    set (rs3 := rs2 # (cond_which_reg f) <- (if b then Vtrue else Vfalse)).
    econstructor 2 with (t1:=E0) (t2:=E0) (s2:=State tf sp (instr_2_pc f v) rs3 m _).
      eapply exec_Iop. transfstep. now rewrite I. transfstep.
        simpl. erewrite same_regvalues with (rs2:=rs) (max:=maxreg f); eauto. now rewrite H.
        intros. unfold rs2, rs1. repeat rewrite Regmap.gso; unfold_all_regs; auto; extlia.
        unfold_regs. intros. eapply max_reg_function_use with (params:=f.(PredRTL.params)) in I; [|enow simpl]; extlia.
    econstructor 2 with (t1:=E0) (t2:=E0) (s2:=State tf sp (set_v_targ_new_pc f v) rs3 m _).
      apply exec_Inop. transfstep. now rewrite I. transfstep.
    set (rs4 := rs3 # (targ_new_reg f) <- (nat2val w')).
    econstructor 2 with (t1:=E0) (t2:=E0) (s2:=State tf sp (set_v_targ_pc f v) rs4 m _).
      eapply exec_Isel. transfstep. rewrite S. eauto. transfstep.
        unfold rs3, rs2, rs1, eval_sel, Vtrue, Vfalse.
        rewrite Regmap.gss. repeat (rewrite Regmap.gso; [|unfold_regs; extlia]).
        rewrite const. rewrite const.
        case b in *; rewrite B; apply Val.normalize_idem; unfold nat2val; constructor.
          { apply vertex_n, vertex_same, successors_spec with (v:=v); [ now apply vertex_same, vertex_n | rewrite S ]. now apply in_cons, in_eq. }
          { apply vertex_n, vertex_same, successors_spec with (v:=v); [ now apply vertex_same, vertex_n | rewrite S ]. now apply in_eq. }
    set (rs5 := rs4 # (targ_reg f) <- (rs4 # (targ_new_reg f))).
    econstructor 2 with (t1:=E0) (t2:=E0) (s2:=State tf sp (closing_pc f v) rs5 m _).
      eapply exec_Isel. transfstep. transfstep.
        unfold rs4, rs3, rs2, eval_sel.
        rewrite Regmap.gso, Regmap.gso, Regmap.gss; try (unfold_regs; extlia).
        rewrite Regmap.gso with (j:=targ_new_reg f) (i:=targ_reg f); [|unfold_regs; extlia].
        case b in *; apply Val.normalize_idem; rewrite Regmap.gss; now unfold nat2val.
    econstructor 2 with (t1:=E0) (t2:=E0) (s2:=State tf sp w rs5 m _).
    case (f.(uniform_cond) v) eqn:?.
      (* uniform *)
      copy I. copy I. apply cond_num_successors in I. rewrite Heqb0 in I.
      case (successors f.(PredRTL.g) v) eqn:?; try case l eqn:?; try case l0 eqn:?; try (simpl in I; lia).
      eapply exec_Icond. transfstep. now rewrite I0, Heqb0.
      rewrite G, (new_successors_2 f v VN). exact Heql.
      simpl. unfold rs5, rs4, rs3. rewrite Regmap.gso, Regmap.gso, Regmap.gss; try (unfold_regs; extlia).
      Unshelve. 20: exact b. now case b.
      unfold w. rewrite B. apply DETOUR_COND_UNIFORM in I1; auto. rewrite Heql, S in I1. simpl in I1. injection I1. now case b.
      (* tainted *)
      copy I. copy I. apply cond_num_successors in I. rewrite Heqb0 in I.
      case (successors f.(PredRTL.g) v) eqn:?; try case l eqn:?; try (simpl in I; lia).
      eapply exec_Inop. transfstep. now rewrite I0, Heqb0.
      unfold uniquesucc. rewrite G, (new_successors_2 f v VN), Heql. 
      assert (VW: v → w' in f.(g_pred)). { apply successors_spec. enow eapply vertex_same, PredRTL.getinstr_vertex. rewrite B, S. case b; [|apply in_cons]; apply in_eq. }
      apply DETOUR_SPEC in VW as []. apply successors_spec in H17; [| enow eapply PredRTL.getinstr_vertex]. rewrite Heql in H17. unfold w. f_equal. now case H17.
    econstructor 1.
    all: eauto.

  econstructor. apply TF. unfold_regs. apply lessdef_new_five; auto; apply def_rev; auto; try extlia.
  now rewrite Regmap.gss, Regmap.gss.
  
  Unshelve.
  solve_regs_constant.
  all: repeat solve_wt.
  1-3: rewrite E, new_type_cond_which_reg; now case b.
  * unfold rs4. rewrite Regmap.gss, E, new_type_targ_reg. constructor.
Qed.

Lemma real_return: forall stk m' o wt (def': PredRTL.def_regset f rs')
  (I: PredRTL.getinstr f v = Some (Ireturn o))
  (SG: successors f.(PredRTL.g) v = nil)
  (SP: successors f.(PredRTL.g_pred) v = nil),
  Mem.free m stk 0 (PredRTL.stacksize f) = Some m' ->
  sp = (Vptr stk Ptrofs.zero) ->
  v = v_targ ->
  exists rs_new,
    plus SelRTL.step tge (State tf sp v rs m wt) E0 (EndState (Internal tf) (regmap_optget o Vundef rs_new) m') /\
    match_states (PredRTL.EndState (Internal f) (regmap_optget o Vundef rs') m') (EndState (Internal tf) (regmap_optget o Vundef rs_new) m').
Proof.
  intros. prepare I. rewrite <- H1 in TARG.

  eexists. split.
    set (rs1 := rs # (v_reg f) <- (nat2val v)).
    econstructor 1 with (t1:=E0) (t2:=E0) (s2:=State tf sp (live_pc f v) rs1 m _).
      eapply exec_Iop. transfstep. transfstep. auto.
    set (rs2 := rs1 # (livereg f) <- Vtrue).
    econstructor 2 with (t1:=E0) (t2:=E0) (s2:=State tf sp (instr_1_pc f v) rs2 m  _).
      eapply exec_Iop. transfstep. auto. transfstep.
      simpl. unfold rs1. rewrite Regmap.gss, Regmap.gso; [|unfold_regs; lia]. rewrite TARG.
      simpl. rewrite nat2int_int_eq; auto; lia.
    econstructor 2 with (t1:=E0) (t2:=E0) (s2:=State tf sp (instr_2_pc f v) rs2 m _).
      apply exec_Inop. transfstep. now rewrite I. transfstep.
    econstructor 2 with (t1:=E0) (t2:=E0) (s2:=State tf sp (set_v_targ_new_pc f v) rs2 m _).
      apply exec_Inop. transfstep. now rewrite I. transfstep.
    econstructor 2 with (t1:=E0) (t2:=E0) (s2:=State tf sp (set_v_targ_pc f v) rs2 m _).
      eapply exec_Inop. transfstep. now rewrite SP. transfstep.
    set (rs3 := rs2 # (targ_reg f) <- (rs2 # (targ_new_reg f))).
    econstructor 2 with (t1:=E0) (t2:=E0) (s2:=State tf sp (closing_pc f v) rs3 m _).
      eapply exec_Isel. transfstep. transfstep.
        unfold rs2, eval_sel.
        rewrite Regmap.gss.
        apply Val.normalize_idem.
        unfold rs1. rewrite Regmap.gso, Regmap.gso; try (unfold_regs; extlia).
        pose (wt (targ_new_reg f)). now rewrite E, new_type_targ_new_reg in h.
    econstructor 2 with (t1:=E0) (t2:=E0) (s2:=EndState (Internal tf) (regmap_optget o Vundef rs3) m').
      rewrite H0. apply exec_Ireturn. transfstep. now rewrite I.
      now rewrite G, (new_successors_2 f v VN), SG.
      now replace tf.(stacksize) with f.(PredRTL.stacksize) by (now unfold transl_function in TF; injection TF; intro X; rewrite <- X).
    econstructor 1.
    all: eauto.
  
  econstructor. unfold transl_fundef, transf_partial_fundef. now rewrite TF.
  case o; auto. intro. unfold_regs. apply lessdef_new_three; auto; apply def_rev; auto; extlia. 

  Unshelve.
  all: repeat solve_wt.
  * unfold rs2, rs1. repeat (rewrite Regmap.gso; [| unfold_regs; extlia]).
    rewrite E, new_type_targ_reg. pose (wt (targ_new_reg f)). now rewrite E, new_type_targ_new_reg in h.
Qed.

End Step7.

Section Init.

Variable f: PredRTL.function.
Variable tf: function.
Variable args: list val.
Variable sp: val.
Variable m: mem.

Hypothesis TF: transl_function f = OK tf.
Hypothesis C: tf.(code) = transl_code f.
Hypothesis G: tf.(g) = transl_graph f.
Hypothesis P: tf.(params) = f.(PredRTL.params).
Hypothesis ST: tf.(stacksize) = f.(PredRTL.stacksize).
Hypothesis SIG: tf.(sig) = f.(PredRTL.sig).
Hypothesis E: tf.(env) = new_env f.
Hypothesis EN: tf.(entry) = new_entry f.
Hypothesis WT: Val.has_type_list args (sig_args f.(PredRTL.sig)).
Hypothesis DEF: def_args args.

Lemma init_sequence_step_1: forall reg wt,
  reg < num_regs f ->
  exists wt', SelRTL.step tge
    (State tf sp (init_reg_pc f reg) (init_all_regs' tf.(env) args tf.(params) reg) m wt) E0
    (State tf sp (init_reg_pc f (S reg)) (init_all_regs' tf.(env) args tf.(params) (S reg)) m wt').
Proof.
  intros. eexists ?[wt']. pose proof num_regs_nonzero f.
  case (in_dec peq (Pos.of_succ_nat reg) f.(PredRTL.params)) eqn:R.
  + generalize dependent ?wt'.
    rewrite init_all_regs_step_unfold_1; [| rewrite P; now replace (Pos.of_nat (S reg)) with (Pos.of_succ_nat reg) by extlia | rewrite P; now apply args_params_same_length | apply DEF ].
    intros. irrel wt w.
    eapply exec_Inop. unfold getinstr. rewrite C, new_code_spec_2; [ unfold init_reg; now rewrite R | auto ].
    unfold uniquesucc, init_reg_pc. rewrite G, new_successors_3. auto. lia.
  + generalize dependent ?wt'.
    rewrite init_all_regs_step_unfold_2; [| rewrite P; now replace (Pos.of_nat (S reg)) with (Pos.of_succ_nat reg) by extlia ].
    intros.
    case (in_dec peq (Pos.of_succ_nat reg) (f.(PredRTL.params))) eqn:?; [congruence|]. case (f.(PredRTL.env) (Pos.of_succ_nat reg)) eqn:?; eauto;
      (eapply exec_Iop;
      [ unfold getinstr; rewrite C, new_code_spec_2; unfold init_reg; [enow rewrite Heqs, Heqt; eauto | lia] 
      | unfold uniquesucc, init_reg_pc; rewrite G, new_successors_3; auto; lia
      | simpl; unfold default_value; rewrite E; rewrite new_type_normal_reg, Heqt; auto; unfold_all_regs; extlia]).
  Unshelve.
  * now apply init_all_regs'_wt.
Qed.

Lemma init_sequence_step_2: forall reg wt,
  reg = num_regs f - 1 ->
  exists wt', SelRTL.step tge
    (State tf sp (init_reg_pc f reg) (init_all_regs' tf.(env) args tf.(params) reg) m wt) E0
    (State tf sp (init_targ_new_pc f) (init_all_regs' tf.(env) args tf.(params) (num_regs f)) m wt').
Proof.
  intros. eexists ?[wt']. pose proof num_regs_nonzero f.
  case (in_dec peq (Pos.of_succ_nat reg) f.(PredRTL.params)) eqn:R.
  + generalize dependent ?wt'. replace (num_regs f) with (S reg) in |- * by lia.
    rewrite init_all_regs_step_unfold_1; [| rewrite P; now replace (Pos.of_nat (S reg)) with (Pos.of_succ_nat reg) by extlia | rewrite P; now apply args_params_same_length | apply DEF ].
    intros. irrel wt w.
    eapply exec_Inop. unfold getinstr. rewrite C, new_code_spec_2; [ unfold init_reg; now rewrite R | auto ]. lia.
    unfold uniquesucc. now rewrite G, H, new_successors_3_init_last.
  + generalize dependent ?wt'. replace (num_regs f) with (S reg) in |- * by lia.
    rewrite init_all_regs_step_unfold_2; [| rewrite P; now replace (Pos.of_nat (S reg)) with (Pos.of_succ_nat reg) by extlia ].
    intros.
    case (in_dec peq (Pos.of_succ_nat reg) (f.(PredRTL.params))) eqn:?; [congruence|]. case (f.(PredRTL.env) (Pos.of_succ_nat reg)) eqn:?; eauto;
      (eapply exec_Iop;
      [ unfold getinstr; rewrite C, new_code_spec_2; unfold init_reg; [enow rewrite Heqs, Heqt; eauto | lia] 
      | unfold uniquesucc; now rewrite G, H, new_successors_3_init_last
      | simpl; unfold default_value; rewrite E; rewrite new_type_normal_reg, Heqt; auto; unfold_all_regs; extlia]).
  Unshelve.
  * replace (num_regs f) with (S reg) by (pose proof num_regs_nonzero f; lia). now apply init_all_regs'_wt.
Qed.

Lemma init_sequence_ind_1: forall reg wt,
  reg < num_regs f ->
  exists wt', star SelRTL.step tge
    (State tf sp (new_entry f) (init_all_regs' tf.(env) args tf.(params) 0) m wt) E0
    (State tf sp (new_entry f + reg) (init_all_regs' tf.(env) args tf.(params) reg) m wt').
Proof.
  intros. induction reg.
  * eexists. replace (new_entry f + 0) with (new_entry f) by lia. constructor.
  * assert (reg < num_regs f) by lia. copy H0. apply IHreg in H0 as [?]. eapply init_sequence_step_1 in H1 as [?].
    eexists. eapply star_right. apply H0. unfold init_reg_pc in H1. apply H1. auto.
Qed.

Lemma init_sequence_step_3a: forall regs wt,
  exists wt', SelRTL.step tge
    (State tf sp (init_targ_new_pc f) regs m wt) E0
    (State tf sp (init_targ_pc f) (regs # (targ_new_reg f) <- (nat2val 0)) m wt').
Proof.
  intros. eexists. econstructor 2.
  * unfold getinstr. rewrite C, new_code_spec_3. enow unfold set_int_reg.
  * unfold uniquesucc. now rewrite G, new_successors_3_targ_new.
  * auto.
  Unshelve.
  apply wt_regset_assign. auto. rewrite E, new_type_targ_new_reg. auto. constructor.
Qed.

Lemma init_sequence_step_3b: forall regs wt,
  exists wt', SelRTL.step tge
    (State tf sp (init_targ_pc f) regs m wt) E0
    (State tf sp (const_reg_pc f 0) (regs # (targ_reg f) <- (nat2val f.(PredRTL.entry))) m wt').
Proof.
  intros. eexists. econstructor 2.
  * unfold getinstr. rewrite C, new_code_spec_4. enow unfold set_int_reg.
  * unfold uniquesucc. now rewrite G, new_successors_3_targ.
  * auto.
  Unshelve.
  apply wt_regset_assign. auto. rewrite E, new_type_targ_reg. auto. constructor.
Qed.

Let start := Pos_to_pred_nat (const_reg f 0).

Ltac unfold_pcs := unfold set_v_pc, live_pc, instr_1_pc, instr_2_pc, set_v_targ_new_pc, set_v_targ_pc, closing_pc,
                    new_N, const_reg_pc, init_targ_pc, init_targ_new_pc, init_reg_pc, new_entry.

Lemma init_sequence_step_4a: forall regs v wt,
  S v < f.(PredRTL.n) ->
  exists wt', SelRTL.step tge
    (State tf sp (const_reg_pc f v) (set_regs_seq regs v start) m wt) E0
    (State tf sp (const_reg_pc f (S v)) (set_regs_seq regs (S v) start) m wt').
Proof.
  unfold start in *. intros. eexists ?[wt'].
  eapply exec_Iop.
  + unfold getinstr. rewrite C, new_code_spec_5. unfold set_int_reg.
    do 2 f_equal. unfold Pos_to_pred_nat. unfold_regs. extlia. extlia.
  + unfold uniquesucc. replace (const_reg_pc f v) with (new_entry f + (const_reg_pc f v - new_entry f)) by (unfold_pcs; extlia).
    rewrite G, new_successors_3. f_equal. unfold_pcs. extlia. unfold_pcs. extlia.
  + auto.
  Unshelve.
  * simpl. apply wt_regset_assign. auto. rewrite E.
    replace (Pos.of_succ_nat (Pos_to_pred_nat (const_reg f 0) + v)) with (const_reg f v) by (unfold Pos_to_pred_nat, const_reg; extlia).
    now rewrite new_type_const_reg.
Qed.

Lemma init_sequence_step_4b: forall regs wt,
  exists wt', SelRTL.step tge
    (State tf sp (const_reg_pc f (f.(PredRTL.n)-1)) (set_regs_seq regs (f.(PredRTL.n)-1) start) m wt) E0
    (State tf sp (PredRTL.entry f) (set_regs_seq regs (S (f.(PredRTL.n)-1)) start) m wt').
Proof.
  unfold start in *. intros. eexists ?[wt']. pose f.(PredRTL.N).
  eapply exec_Iop.
  + unfold getinstr. rewrite C, new_code_spec_5. unfold set_int_reg.
    do 2 f_equal. unfold Pos_to_pred_nat. unfold_regs. extlia. extlia.
  + unfold uniquesucc. replace (const_reg_pc f (f.(PredRTL.n)-1)) with (new_N f - 1) by (unfold_pcs; extlia).
    now rewrite G, new_successors_4.
  + auto.
  Unshelve.
  * simpl. apply wt_regset_assign. auto. rewrite E.
    replace (Pos.of_succ_nat (Pos_to_pred_nat (const_reg f 0) + _)) with (const_reg f (f.(PredRTL.n)-1)) by (unfold Pos_to_pred_nat, const_reg; extlia).
    now rewrite new_type_const_reg.
Qed.

Lemma init_sequence_ind_4: forall v regs wt,
  v < f.(PredRTL.n) ->
  exists wt', star SelRTL.step tge
    (State tf sp (const_reg_pc f 0) regs m wt) E0
    (State tf sp (const_reg_pc f v) (set_regs_seq regs v start) m wt').
Proof.
  intros. induction v.
  * eexists. simpl. constructor.
  * assert (v < f.(PredRTL.n)) by lia. apply IHv in H0 as [?]. eapply init_sequence_step_4a in H as [?].
    eexists. eapply star_right. apply H0. apply H. auto.
Qed.

Lemma init_sequence: forall m' init init' regs stk pd wt def wt1 def1,
  sp = (Vptr stk Ptrofs.zero) ->
  Mem.alloc m' 0 f.(PredRTL.stacksize) = (m, stk) ->
  init = init_all_regs f.(PredRTL.env) f.(PredRTL.code) f.(PredRTL.params) args ->
  init' = init # (targ_new_reg f) <- (nat2val 0) # (targ_reg f) <- (nat2val f.(PredRTL.entry)) ->
  regs = set_regs_seq init' f.(PredRTL.n) start ->
  exists wt',
    plus SelRTL.step tge (InitState (Internal tf) args m' wt def) E0 (State tf sp f.(PredRTL.entry) regs m wt') /\
    match_states (PredRTL.State f sp f.(PredRTL.entry) init m f.(PredRTL.entry) pd wt1 def1) (State tf sp f.(PredRTL.entry) regs m wt').
Proof.
  intros. eexists ?[wt']. pose proof num_regs_nonzero f. pose proof f.(PredRTL.N).
  (* The sequence proceeds like this:
     exec_function_internal -> ind1 -> step2 -> step3a -> step3b -> ind4 -> step4b *)
  split.
  * econstructor.
      { eapply exec_function_internal; enow rewrite ST. }

    assert (N1: num_regs f - 1 < num_regs f) by lia.
    eapply init_sequence_ind_1 in N1 as [? N1].
    eapply star_trans.
      { simpl in N1. rewrite <- H, EN.  apply N1. }

    assert (N2: num_regs f - 1 = num_regs f - 1) by lia.
    eapply init_sequence_step_2 in N2 as [? N2].
    eapply star_left.
      { replace (new_entry f + (num_regs f - 1)) with (init_reg_pc f (num_regs f - 1)) by now unfold init_reg_pc.
        apply N2. }

    exploit init_sequence_step_3a. intros [? N3].
    eapply star_left. { apply N3. }

    exploit init_sequence_step_3b. intros [? N4].
    eapply star_left. { apply N4. }

    assert (N5: f.(PredRTL.n)-1 < f.(PredRTL.n)) by lia.
    eapply init_sequence_ind_4 in N5 as [? N5].
    eapply star_trans. { apply N5. }

    exploit init_sequence_step_4b. intros [? N6].
    eapply star_left. { apply N6. }

    { clear N1. clear N2. clear N3. clear N4. clear N5. clear N6. clear x. clear x0. clear x1. clear x2. clear x3.
      generalize dependent x4. generalize dependent ?wt'.
      rewrite H3, H2, H1. unfold init_all_regs, num_regs, maxreg. rewrite P.
      replace (S (f.(PredRTL.n)-1)) with f.(PredRTL.n) by (pose proof f.(PredRTL.N); lia).
      replace (init_all_regs' (env tf) _ _ _) with (init_all_regs' f.(PredRTL.env) args (PredRTL.params f) (Pos.to_nat (max_reg_function (PredRTL.code f) (PredRTL.params f)))).
      2: { apply init_all_regs'_env_inv, env_inv_conv. intros. rewrite E, new_type_normal_reg. auto. now unfold maxreg. }
      intros. irrel w x4. apply star_refl. }

    Unshelve. all: auto.

    (* Remaining welltypedness *)
    + assert (wt_regset (env tf) init).
      { eapply wt_regset_env_inv; [ rewrite H1; apply init_all_regs_def | | apply wt1 ].
        intros. rewrite E, new_type_normal_reg. auto. now unfold maxreg. }
      assert (wt_regset (env tf) init'). 
      { rewrite H2. apply wt_regset_assign. apply wt_regset_assign. auto.
        now rewrite E, new_type_targ_new_reg.
        now rewrite E, new_type_targ_reg. }
      assert (wt_regset (env tf) regs).
      { rewrite H3. apply set_regs_seq_wt; auto.
        intros. replace (Pos.of_succ_nat r) with (const_reg f (r - start)).
         rewrite E, new_type_const_reg. auto.
         unfold start, const_reg, Pos_to_pred_nat in *. extlia. }
      auto.
    + apply RTLtyping.wt_init_regs. destruct f.(PredRTL.WELLTYPED).
      rewrite E, P. replace (map (new_env f) f.(PredRTL.params)) with (map f.(PredRTL.env) f.(PredRTL.params)).
      now rewrite wt_params, <- SIG.
      apply list_map_exten. intros. apply new_type_normal_reg. unfold maxreg.
      now apply max_reg_function_params.

  (* Match States *)
  * constructor; auto.
    + apply regs_lessdef_trans with (r2:=init'); auto.
      - rewrite H2. apply lessdef_new_two. apply regs_lessdef_refl.
        rewrite H1. unfold init_all_regs. erewrite init_all_regs'_undef_spec_2, rtl_init_regs_undef_spec.
          auto. intros. enow apply max_reg_function_params with (code:=f.(PredRTL.code)). unfold_regs; extlia. unfold_regs; extlia.
        rewrite H1. unfold init_all_regs. erewrite init_all_regs'_undef_spec_2, rtl_init_regs_undef_spec.
          auto. intros. enow apply max_reg_function_params with (code:=f.(PredRTL.code)). unfold_regs; extlia. unfold_regs; extlia.
      - rewrite H3. apply set_regs_seq_lessdef_2.
        intros. rewrite H2, Regmap.gso, Regmap.gso; try (unfold start, Pos_to_pred_nat; unfold_regs; extlia).
        rewrite H1. unfold init_all_regs. erewrite init_all_regs'_undef_spec_2, rtl_init_regs_undef_spec; auto.
      ** intros. enow apply max_reg_function_params with (code:=f.(PredRTL.code)).
      ** unfold start, Pos_to_pred_nat. unfold_regs. extlia.
      ** unfold start, Pos_to_pred_nat. unfold_regs. extlia.
    + rewrite <- succpred with (p:=targ_reg f), H3, H2, H1, set_regs_seq_old.
      now rewrite succpred, Regmap.gss.
      unfold start, Pos_to_pred_nat. unfold_regs. extlia.
    + rewrite H3. replace start with (Pos.to_nat (cond_which_reg f)) by (unfold start, Pos_to_pred_nat; unfold_regs; extlia).
      apply set_regs_are_constant.
Qed.

End Init.

Lemma match_states_regs_lessdef:
  forall f sp v rs (m: mem) v_targ pd wt def tf m rs' rs'' wt' def' wt'',
  regs_lessdef rs' rs ->
  match_states (PredRTL.State f sp v rs m v_targ pd wt def) (SelRTL.State tf sp v rs'' m wt'') ->
  match_states (PredRTL.State f sp v rs' m v_targ pd wt' def') (SelRTL.State tf sp v rs'' m wt'').
Proof.
  intros. inv H0. constructor; auto.
  enow eapply regs_lessdef_trans.
Qed.

Theorem transl_step_correct:
  forall s1 t s2
  (EM: state_emergent prog s1),
  PredRTL.step ge s1 t s2 ->
  forall ts1 (MS: match_states s1 ts1),
  exists ts2, plus SelRTL.step tge ts1 t ts2 /\ match_states s2 ts2.
Proof.
  intros. inv MS.
  assert (C: tf.(code) = transl_code f) by (now unfold transl_function in TF; injection TF; intro X; rewrite <- X).
  assert (G: tf.(g) = transl_graph f) by (now unfold transl_function in TF; injection TF; intro X; rewrite <- X).
  assert (EE: tf.(env) = new_env f) by (now unfold transl_function in TF; injection TF; intro X; rewrite <- X).
  assert (VN: v < f.(PredRTL.n)) by (apply N_VS; now destruct pd as [?[]]).
  assert (VTN: v_targ < f.(PredRTL.n)) by (apply N_VS; now destruct pd as [?[]]).
  pose proof f.(N_MAX) as S.
  decompose [and] (new_code_spec_1 f v VN). decompose [and] (new_successors_1 f v VN).
  + inv H.
  * case i eqn:?.
  - eapply dummy_nop with (v:=v) in TF; eauto. decompose [ex and] TF. enow eexists.
  - copy I. eapply PredRTL.op_is_safe, execute_Iop with (env:=f.(PredRTL.env)) in I0 as [opres E]; eauto.
    2: eapply wt_instr_at; eauto; apply PredRTL.WELLTYPED.
    eapply dummy_op with (v:=v) in TF; eauto. decompose [ex and] TF. enow eexists.
    enow eapply ControlFlowSecurity.uni_chain_path.
  - exfalso. apply ControlFlowSecurity.uni_chain_path in EM; eauto. now apply UNI_MEM in I.
  - eapply uniquesucc_edge_succs_full in U as []; eauto. apply SUCCS_PRED in I. now rewrite H in I.
  - assert (v = f.(PredRTL.exit)) by (enow apply return_exit; eexists).
    apply PredRTL.EXIT in H as []. eapply uniquesucc_edge_succs_full in U as []; eauto. congruence.
  - now apply PredRTL.SAFE in I.
  * eapply dummy_cond with (v:=v) in TF; eauto. decompose [ex and] TF. enow eexists.
    enow eapply eval_condition_lessdef; [ eapply regs_lessdef_regs | apply Mem.extends_refl |].
  * eapply real_nop with (v:=v_targ) in TF; eauto. decompose [ex and] TF. enow eexists.
  * eapply real_op with (v:=v_targ) in TF; eauto. decompose [ex and] TF. enow eexists.
  * eapply real_load with (v:=v_targ) in TF; eauto. decompose [ex and] TF. enow eexists.
  * eapply real_cond with (v:=v_targ) in TF; eauto. decompose [ex and] TF. enow eexists.
    enow eapply eval_condition_lessdef; [ eapply regs_lessdef_regs | apply Mem.extends_refl |].
  * eapply real_return with (v:=v_targ) in TF; eauto. decompose [ex and] TF. enow eexists.
    case (successors f.(g_pred) v_targ) eqn:?; auto. assert (v_targ → v in f.(g_pred)) by (apply successors_spec; [ enow eapply vertex_same, PredRTL.getinstr_vertex | rewrite Heql; apply in_eq ]).
    apply DETOUR_SPEC in H as []. apply successors_spec in H. now rewrite H22 in H. enow eapply PredRTL.getinstr_vertex.
  + inv H. case tf in *; [| simpl in TF; congruence].
    assert (C: f.(code) = transl_code f0) by (now unfold transl_function in TF; injection TF; intro X; rewrite <- X).
    simpl.
  * eapply init_sequence in C; eauto. decompose [ex and] C. eexists; eauto.
    all: try (now unfold transl_function in TF; injection TF; intro X; rewrite <- X).
  * case tf in *; [simpl in TF; congruence |].
    eexists. split; [|constructor]. apply plus_one. constructor. eapply external_call_symbols_preserved. eapply senv_preserved. eauto.
    unfold transl_fundef in TF; injection TF; intro X; rewrite <- X. exact H5. exact TF. auto.
  + inv H.
Qed.

Theorem transf_program_correct:
  forward_simulation (PredRTL.semantics prog) (SelRTL.semantics tprog).
Proof.
  eapply forward_simulation_plus with
    (match_states := fun s1 s2 => match_states s1 s2 /\ state_emergent prog s1).
- apply senv_preserved.
- intros. exploit transl_initial_states; eauto.
  intros [i []]. exists i. split; auto. split; auto. now apply state_emergent_init.
- intros. destruct H. eapply transl_final_states; eauto.
- intros. decompose [ex and] H0. exploit transl_step_correct; eauto.
  intros [s2' [A B]]. exists s2'; split; auto. split; auto. enow eapply state_emergent_step.
Qed.

End Preservation.