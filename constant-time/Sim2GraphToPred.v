Require Import Axioms Common Coqlib Classical Datatypes.
Require Import AST Memory Registers Maps Values Events Globalenvs Smallstep Op Integers.
Require Import TaintAnalysis ControlFlowSecurity.
Require Import ListsExtra Graph GraphDual PredRTL GraphRTL SharedTypes SafeOpProof.
Require Import Before.
Require Import PCFL PCFLBranchMapping PCFLEdgeEmbedding.
Require Import Smallstep Errors Linking.


Section Translation.

Variable f: GraphRTL.function.

Section Uniform.

Variable uniform_cond: V -> bool.

Definition pcfl := pcfl f uniform_cond.

Definition new_target := new_target f uniform_cond.
Definition detour v w := match edge_dec f.(g) v w with
  | left vw => new_target v w vw
  | _ => 0
end.

Lemma DETOUR_SPEC:
  forall v w, v → w in f.(g) -> v → (detour v w) in pcfl /\ postdom pcfl f.(exit) w (detour v w).
Proof.
  intros. exploit (new_target_spec f uniform_cond v w). Unshelve. 2: exact H.
  intro. unfold detour. case edge_dec; try contradiction.
  intro. now irrel e H. 
Qed.

Lemma DETOUR_CHAIN:
  forall v w, v → w in f.(g) -> w <> (detour v w) -> chain_inv f uniform_cond w (detour v w).
Proof.
  intros. exploit (new_target_chain f uniform_cond v w). Unshelve. 3: exact H.
  intro. unfold detour in H0. case edge_dec in H0; try contradiction. unfold new_target in H0. now irrel_in H1 H e.
  unfold detour. case edge_dec; try contradiction. unfold new_target. intros. now irrel e H.
Qed.

Lemma cond_successors_pcfl_tainted: forall v c args,
  f.(code) @! v = Some (SharedTypes.Icond c args) ->
  uniform_cond v = false <-> length (successors pcfl v) = 1.
Proof.
  intros.
  assert (vertex f.(g) v) by enow eapply getinstr_vertex.
  assert (v <> f.(exit)) by (intro; apply return_exit in H1 as []; congruence).
  destruct (uniform_cond v) eqn:?; split; try easy; intro.
  * eapply new_successors_uniform_length with (f:=f) in Heqb; auto.
    unfold pcfl, n, PCFLBranchMapping.step in *.
    rewrite Heqb in H2 at 1. apply f.(SUCCS) in H. simpl in H. lia.
  * eapply new_successors_tainted with (f:=f) in Heqb; eauto.
    Unshelve. all: auto.
    unfold pcfl, n, PCFLBranchMapping.step in *.
    erewrite Heqb at 1; simpl; lia.
Qed.

Lemma cond_successors_pcfl_uniform: forall v c args,
  f.(code) @! v = Some (SharedTypes.Icond c args) ->
  uniform_cond v = true ->
  successors pcfl v = map (detour v) (successors f.(g) v).
Proof.
  intros. unfold pcfl, PCFL.pcfl. erewrite new_successors_uniform; eauto.
    Unshelve. 2: enow eapply getinstr_vertex. 2: intro; apply return_exit in H1 as []; congruence.
  unfold uniform_successors.
  eapply map_equal_nth.
  * symmetry. apply map_extra_id_length.
  * intros. rem proj2_sig.
    assert (i < length (successors (g f) v)) by enow erewrite map_extra_id_length. 
    unfold detour, new_target. case edge_dec eqn:?.
    + eassert (! (nth i (! (map_extra_id (successors f.(g) v) (edge f.(g) v) _)) d1) = nth i (successors f.(g) v) d2)
        by (now rewrite map_extra_id_nth; [ apply nth_indep | exact Nat.eq_dec |]).
      generalize e. rewrite <- H3. intros. now irrel e0 y.
    + exfalso. enow apply n, successors_spec; [ eapply getinstr_vertex | apply nth_In ]. 
Qed.

Lemma succs_g: forall pc i,
  f.(code) @! pc = Some i ->
  min_successors i <= length (successors pcfl pc) <= num_successors i.
Proof.
  intros.
  pose proof f.(SUCCS) pc i H.
  assert (vertex f.(g) pc) by enow eapply getinstr_vertex.
  case (Nat.eq_dec pc f.(exit)) eqn:?.
  + copy e. apply f.(EXIT) in e0 as []. rewrite H3 in H0.
    case i in *; simpl in *; try congruence.
    copy e. eapply unique_exit_pcfl in e0 as [].
    unfold pcfl, PCFL.pcfl, PCFLEdgeEmbedding.step in *. now rewrite H5.
  + copy n. apply has_successors_pcfl with (u:=uniform_cond) in n0; auto.
    apply less_successors_pcfl with (u:=uniform_cond) in H1.
    unfold pcfl, PCFL.pcfl, PCFLEdgeEmbedding.step in *.
    split; [|lia]. case successors eqn:? at 1; [congruence|].
    case i; simpl; lia.
Qed.

End Uniform.

(*** Translation function using the hack-moll algorithm ***)
Definition transl_function: PredRTL.function :=
  PredRTL.mkfunction
    f.(code)
    f.(sig)
    f.(params)
    f.(stacksize)
    (pcfl f.(uniform_cond))
    f.(entry)
    f.(exit)
    f.(n)
    f.(uniform_cond)
    f.(g)
    (detour f.(uniform_cond))
    (DETOUR_SPEC f.(uniform_cond))
    (cond_successors_pcfl_uniform f.(uniform_cond))
    f.(idx)
    ltac:(apply top_sort_retained)
    f.(IDX)
    f.(N)
    f.(N_MAX)
    f.(VS)
    f.(NCODE)
    f.(SUCCS)
    (succs_g f.(uniform_cond))
    ltac:(apply cond_successors_pcfl_tainted)
    f.(ENTRY)
    ltac:(intro v; eapply iff_trans; [apply f.(EXIT) | apply unique_exit_remains])
    f.(EXIT)
    ltac:(auto)
    (DETOUR_CHAIN f.(uniform_cond))
    f.(taint_attr)
    f.(TAINT_RES)
    f.(UNIFORM)
    f.(SAFE)
    f.(UNI_MEM)
    f.(env)
    f.(ANYFREE)
    f.(WELLTYPED).

End Translation.


Definition transl_fundef := transf_fundef transl_function.
Definition transf_program (p: program) : PredRTL.program := transform_program transl_fundef p.


(*** SEMANTIC MATCH AND PRESERVATION ***)

Inductive match_states: GraphRTL.state -> PredRTL.state -> Prop :=
  | match_state:
      forall f sp v rs m C wt wt' def def'
      (SP: exists b ofs, sp = Vptr b ofs),
      match_states (GraphRTL.State f sp v rs m wt def) (PredRTL.State (transl_function f) sp v rs m v C wt' def')
  | match_initstate:
      forall args f m wt wt' def,
        match_states (GraphRTL.InitState f args m wt def) (PredRTL.InitState (transl_fundef f) args m wt' def)
  | match_endstate:
      forall f v m,
        match_states (GraphRTL.EndState f v m) (PredRTL.EndState (transl_fundef f) v m).

Definition match_prog (p: GraphRTL.program) (tp: PredRTL.program) :=
  match_program (fun cu f tf => tf = transl_fundef f) eq p tp.

Lemma transf_program_match: forall p, match_prog p (transf_program p).
Proof.
  intros. apply match_transform_program.
Qed.

Section Preservation.

Variable prog: GraphRTL.program.
Variable tprog: PredRTL.program.
Hypothesis TRANSL: match_prog prog tprog.

Let ge : GraphRTL.genv := Genv.globalenv prog.
Let tge : PredRTL.genv := Genv.globalenv tprog.

(* Trivial boilerplate *)

Lemma symbols_preserved:
  forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
Proof (Genv.find_symbol_transf TRANSL).

Lemma senv_preserved:
  Senv.equiv (Genv.to_senv ge) (Genv.to_senv tge).
Proof (Genv.senv_transf TRANSL).

Lemma function_ptr_translated:
  forall (b: block) (f: GraphRTL.fundef),
  Genv.find_funct_ptr ge b = Some f ->
  Genv.find_funct_ptr tge b = Some (transl_fundef f).
Proof (Genv.find_funct_ptr_transf TRANSL).

Lemma sig_function_translated:
  forall f,
  PredRTL.funsig (transl_fundef f) = GraphRTL.funsig f.
Proof.
  now destruct f.
Qed.

(* Initial and final states *)

Lemma transl_initial_states:
  forall S, GraphRTL.initial_state prog S ->
  exists R, PredRTL.initial_state tprog R /\ match_states S R.
Proof.
  intros. inv H.
  exploit function_ptr_translated. eauto. intro.
  eexists (PredRTL.InitState (transl_fundef f) nil m0 _ _). split.
    econstructor.
  - now apply (Genv.init_mem_transf TRANSL).
  - replace (prog_main tprog) with (prog_main prog). rewrite symbols_preserved. eauto.
    symmetry. eapply match_program_main. eauto.
  - exact H.
  - now constructor.
  Unshelve. rewrite <- FS. now apply sig_function_translated.
Qed.

Lemma transl_final_states:
  forall S R r,
  match_states S R -> GraphRTL.final_state S r -> PredRTL.final_state R r.
Proof.
  intros. inv H0. inv H. constructor.
Qed.


(* Step *)

Section StepSim.

Variable f: function.
Let f' := transl_function f.

Notation "v ▷ w" := (postdom (PredRTL.g f') (PredRTL.exit f') w v) (at level 49).

Lemma transl_uniquesucc:
  forall v w',
  uniquesucc f v = Some w' ->
  exists w, PredRTL.uniquesucc f' v = Some (w, w').
Proof.
  intros. unfold uniquesucc, PredRTL.uniquesucc, transl_function in *. simpl.
  case (successors f.(g) v) eqn:?; try case l eqn:?; try congruence.
  injection H. intro. exists (PredRTL.detour f' v v0). simpl. now rewrite H0.
Qed.

Lemma vertex_f_f': forall x,
  vertex f.(g) x <-> vertex f'.(PredRTL.g) x.
Proof.
  intros. now rewrite vertex_same.
Qed.

Lemma postdom_refl: forall w,
  vertex f.(g) w -> w ▷ w.
Proof.
  intros. apply postdom_refl. now apply PredRTL.EXIT. now apply vertex_f_f'.
Qed.

Lemma getinstr_none: forall x,
  PredRTL.getinstr f' x = None <-> ~ x < f.(n).
Proof.
  intros. unfold PredRTL.getinstr. split; intro.
  * intro. apply f.(NCODE) in H. contradiction. auto.
  * remember ((PredRTL.code f') @! x) as X. case_eq X; intros. 2: auto. assert (X <> None) by congruence.
    rewrite HeqX in H1. apply f'.(PredRTL.NCODE) in H1. easy.
Qed.



Lemma silent_step:
  forall w x sp rs m (pd1: x ▷ w) wt def,
  ~ uni f.(taint_f) f.(TAINT_RES) x ->
  x <> w ->
  exists y (pd2: y ▷ w),
  PredRTL.step tge (PredRTL.State f' sp x rs m w pd1 wt def) E0 (PredRTL.State f' sp y rs m w pd2 wt def).
Proof.
  intros.
  assert (vertex f.(g) x) by (destruct pd1; rewrite vertex_f_f'; easy).
  case (PredRTL.getinstr f' x) eqn:?; [| now apply vertex_n, getinstr_none in H1].
  case i in *.
  * copy Heqo. apply f.(SUCCS) in Heqo. simpl in Heqo. case (successors f.(g) x) eqn:?; [easy|]. case l eqn:?; [|easy].
    repeat eexists. econstructor; eauto. unfold PredRTL.uniquesucc. unfold transl_function. simpl. rewrite Heql. eauto.
  Unshelve.
  + unfold transl_function. simpl. pose proof (DETOUR_SPEC f (uniform_cond f) x v) as [].
    apply successors_spec; auto; rewrite Heql; apply in_eq.
    eapply postdom_edge; eauto; now apply f.(EXIT).
  * copy Heqo. apply f.(SUCCS) in Heqo. simpl in Heqo. case (successors f.(g) x) eqn:?; [easy|]. case l0 eqn:?; [|easy].
    repeat eexists. econstructor; eauto. unfold PredRTL.uniquesucc. unfold transl_function. simpl. rewrite Heql0. eauto.
  Unshelve.
  + unfold transl_function. simpl. pose proof (DETOUR_SPEC f (uniform_cond f) x v) as [].
    apply successors_spec; auto; rewrite Heql0; apply in_eq.
    eapply postdom_edge; eauto; now apply f.(EXIT).
  * exfalso. enow apply PredRTL.UNI_MEM in Heqo. (* load statement cannot be predicated *)
  * copy Heqo. apply f.(SUCCS) in Heqo. simpl in Heqo. case (successors f.(g) x) eqn:?; [easy|]. case l0 eqn:?; [easy|]. case l1 eqn:?; [|easy].
    copy wt. eapply execute_Icond with (cond:=c) in wt0 as [b]. Unshelve.
    + repeat eexists. econstructor 2; eauto.
    + eauto.
    + enow apply f.(SAFE) in Heqo0.
    + intros. eapply Ple_trans with (r:=max_reg_function _ _); [ now apply max_reg_instr_uses with (i:=Icond c l) | enow eapply max_reg_instr_function ].
    + apply PredRTL.WELLTYPED in Heqo0. eauto.
    + eexact def.
    Unshelve.
    enow eapply postdom_kept_cond. 
  * (* return statement cannot be predicated *)
    exfalso. apply f.(SUCCS) in Heqo. simpl in Heqo. case (successors f.(g) x) eqn:?; [|easy].
    assert (x = exit f) by now apply f.(EXIT).
    now apply postdom_spec in pd1 as []; [congruence | easy | apply f.(EXIT) | unfold postdom in pd1 | unfold postdom in pd1].
  * apply f.(SAFE) in Heqo. contradiction.
Qed.

Theorem silent_postdom:
  forall x w sp rs m wt def
  (pd1: x ▷ w)
  (EM: state_emergent tprog (PredRTL.State f' sp x rs m w pd1 wt def)),
  exists pd2,
  star PredRTL.step tge (PredRTL.State f' sp x rs m w pd1 wt def) E0 (PredRTL.State f' sp w rs m w pd2 wt def).
Proof.
  intros.
  pose (P := fun v =>
    forall (pd1: v ▷ w) (EM: state_emergent tprog (PredRTL.State f' sp v rs m w pd1 wt def)),
    exists pd2 : postdom (PredRTL.g f') (PredRTL.exit f') w w,
    star PredRTL.step tge (PredRTL.State f' sp v rs m w pd1 wt def) E0 (PredRTL.State f' sp w rs m w pd2 wt def)
  ).
  enough (P x) by auto. eapply graph_ind_dual with (P:=P).
  * exact f'.(top_sort_g).
  * unfold P in *. intros. assert (vertex f'.(PredRTL.g) w) by now destruct pd1. assert (vertex f.(g) w) by now apply vertex_f_f'.
    case (Nat.eq_dec v w); intro.
    + subst. exists pd0. constructor.
    + exists (postdom_refl w H2). eapply silent_step in n as [y [pd]]; eauto. econstructor. exact H3.
      assert (v → y in f'.(PredRTL.g)) by enow eapply PredRTL.step_is_edge. destruct (H0 y H4 pd) as [pd'].
      - enow eapply state_emergent_step.
      - replace pd' with (postdom_refl w H2) in *. exact H5. apply proof_irr.
      - auto.
      - intro. apply ControlFlowSecurity.uni_chain_path in EM0; auto.
  * now destruct pd1, a.
Qed.

End StepSim.

Lemma split_left: forall (A B: Prop), (A -> B) -> A -> A /\ B.
Proof.
  intros. split. auto. now apply H in H0.
Qed.

Theorem transl_step_correct:
  forall s1 t s2,
  GraphRTL.step ge s1 t s2 ->
  forall ts1 (MS: match_states s1 ts1) (EM: state_emergent tprog ts1),
  exists ts2, (plus PredRTL.step tge ts1 t ts2 /\ state_emergent tprog ts2) /\ match_states s2 ts2.
Proof.
  intros. inv MS.
  assert (DEF: GraphRTL.def_regset f = PredRTL.def_regset (transl_function f)) by auto.
  + inv H; pose (transl_function f) as tf.
  * eapply transl_uniquesucc in H8 as [w]; eauto.
    copy H. eapply uniquesucc_edge_full in H as [? []]; eauto.

    assert (postdom (PredRTL.g tf) (PredRTL.exit tf) pc' pc') by enow eapply postdom_refl.
    eassert (PredRTL.step tge (PredRTL.State tf sp v rs m v C wt def') E0
                                (PredRTL.State tf sp w rs m pc' H2 wt def')) by enow constructor 3.
    exists (PredRTL.State tf sp pc' rs m pc' H3 wt def').
    split. apply split_left.
    ++ intro. enow eapply state_emergent_plus.
    ++ eapply plus_left; eauto. irrel wt' wt. apply H4.
       apply state_emergent_step in H4; [|now irrel wt wt']. irrel_in H4 wt wt'.
       pose proof (silent_postdom f w pc' sp rs m wt' def' H2 H4) as [].
       irrel_in H5 x H3. irrel wt wt'.
       eexact H5. auto.
    ++ constructor 1.
    Unshelve. all: eauto.

  * copy U. eapply transl_uniquesucc in U0 as [w]. copy H.
    eapply uniquesucc_edge_full in H as [? []]; eauto.

    assert (wt'': SharedTypes.wt_regset (env f) rs # res <- v0) by
      (eapply wt_exec_Iop; eauto; enow eapply wt_instr_in_function).
    assert (def'': GraphRTL.def_regset f rs # res <- v0) by enow eapply op_step_def.
    rewrite DEF in def''.

    assert (postdom (PredRTL.g tf) (PredRTL.exit tf) pc' pc') by enow eapply postdom_refl.
    eassert (PredRTL.step tge (PredRTL.State tf sp v rs m v C wt' def') E0
                                (PredRTL.State tf sp w (rs # res <- v0) m pc' _ _ _)) by
                                constructor 4 with (op:=op) (args:=args).
    exists (PredRTL.State tf sp pc' (rs # res <- v0) m pc' H3 wt'' def'').
    split. apply split_left.
    ++ intro. enow eapply state_emergent_plus.
    ++ eapply plus_left; eauto.
       irrel_f_in H4 SharedTypes.wt_exec_Iop wt''. irrel_f_in H4 PredRTL.op_step_def def''.
       apply state_emergent_step in H4; auto.
       pose proof (silent_postdom f w pc' sp (rs # res <- v0) m wt'' def'' H2 H4) as [].
       - irrel_in H5 x H3. irrel_f SharedTypes.wt_exec_Iop wt''. irrel_f PredRTL.op_step_def def''. eauto.
       - auto.
    ++ irrel_f op_step_def def'. irrel_f SharedTypes.wt_exec_Iop wt'.
       constructor 1.
    Unshelve. all: eauto.
    erewrite eval_operation_preserved. eauto. apply symbols_preserved.

  * copy U. eapply transl_uniquesucc in U0 as [w]. copy H.
    eapply uniquesucc_edge_full in H as [? []]; eauto.

    assert (wt'': SharedTypes.wt_regset (env f) rs # dst <- v0) by
      (eapply wt_exec_Iload; eauto; enow eapply wt_instr_in_function).
    assert (def'': GraphRTL.def_regset f rs # dst <- v0) by enow eapply load_step_def.
    rewrite DEF in def''.

    assert (postdom (PredRTL.g tf) (PredRTL.exit tf) pc' pc') by enow eapply postdom_refl.
    eassert (PredRTL.step tge (PredRTL.State tf sp v rs m v C wt' def') E0
                                (PredRTL.State tf sp w (rs # dst <- v0) m pc' _ _ _)).
    { constructor 5; eauto. erewrite eval_addressing_preserved in AD; eauto. symmetry. apply symbols_preserved. }
    exists (PredRTL.State tf sp pc' (rs # dst <- v0) m pc' H3 wt'' def'').
    split. apply split_left.
    ++ intro. enow eapply state_emergent_plus.
    ++ eapply plus_left; eauto.
       apply state_emergent_step in H4; auto.
       pose proof (silent_postdom f w pc' sp (rs # dst <- v0) m wt'' def'' H2) as [].
       - irrel_f_in H4 SharedTypes.wt_exec_Iload wt''. irrel_f_in H4 PredRTL.load_step_def def''. eauto.
       - irrel_in H5 x H3. irrel_f SharedTypes.wt_exec_Iload wt''. irrel_f PredRTL.load_step_def def''. apply H5.
       - auto.
    ++ irrel_f load_step_def def'. irrel_f SharedTypes.wt_exec_Iload wt'.
       constructor 1.
    Unshelve. all: eauto.

  * replace (g f) with (PredRTL.g_pred tf) in H8 by auto.
    copy H8. eapply cond_edge_full in H8 as [? []]; eauto.
    remember (if b then ifso else ifnot) as pc'.
    remember (PredRTL.detour tf v pc') as w.

    rewrite <- Heqpc' in *. rewrite <- Heqw in *.
    assert (postdom (PredRTL.g tf) (PredRTL.exit tf) pc' pc') by enow eapply postdom_refl.
    eassert (PredRTL.step tge (PredRTL.State tf sp v rs m v C wt' def') E0
                                (PredRTL.State tf sp w rs m pc' H2 wt' def')).
                                { generalize H2. dependent rewrite Heqw. econstructor 6; eauto. }
    eexists (PredRTL.State tf sp pc' rs m pc' H3 wt' def').
    split. apply split_left.
    ++ intro. enow eapply state_emergent_plus.
    ++ eapply plus_left; eauto.
       apply state_emergent_step in H4; auto.
       pose proof (silent_postdom f w pc' sp rs m wt' def' H2 H4) as [].
       irrel_in H5 wt1 wt. irrel_in H5 x H3. apply H5. auto.
    ++ irrel def1 def. irrel wt1 wt.
       constructor 1. auto.
  
  * eexists. split. 2: constructor.
     apply split_left.
     ++ intro. enow eapply state_emergent_plus.
     ++ apply plus_one. constructor; eauto.
        apply unique_exit_remains. unfold is_exit. split; auto. destruct C. subst. simpl in v0. enow eapply result_vertex.
  
  + inv H.
  * pose (transl_function f0) as f'.
    eexists. split. 2: constructor. apply split_left. intro. enow eapply state_emergent_plus.
    apply plus_one. irrel wt1 wt'. enow constructor 7. enow eexists.
  * eexists. split. 2: constructor. apply split_left. intro. enow eapply state_emergent_plus.
    apply plus_one. constructor. eapply external_call_symbols_preserved. eapply senv_preserved. eauto.

  + inv H.
Unshelve. apply f.(uniform_cond).
Qed.

Theorem transf_program_correct:
  forward_simulation (GraphRTL.semantics prog) (PredRTL.semantics tprog).
Proof.
  eapply forward_simulation_plus with
    (match_states := fun s1 s2 => match_states s1 s2 /\ state_emergent tprog s2).
- apply senv_preserved.
- intros. exploit transl_initial_states; eauto.
  intros [i []]. exists i. split; auto. split; auto. now apply state_emergent_init.
- intros. destruct H. eapply transl_final_states; eauto.
- intros. destruct H0. exploit transl_step_correct; eauto.
  intros [s2' [[A B] C]]. exists s2'; split; auto.
Qed.

End Preservation.