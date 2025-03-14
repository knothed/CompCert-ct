Require Import Common Coqlib Classical Datatypes.
Require Import AST RTL Memory Registers Maps Values Events Globalenvs Smallstep Op Integers.
Require Import ListsExtra Graph SelRTL SharedTypes.
Require Import Smallstep Errors Linking.

Definition convert_instruction (succs: list positive) (i: instruction) := match i, succs with
  | Inop, s::nil => Some (RTL.Inop s)
  | Iop op args res, s::nil => Some (RTL.Iop op args res s)
  | Iload chunk addr args dst, s::nil => Some (RTL.Iload chunk addr args dst s)
  | Icond cond args, s1::s2::nil => Some (RTL.Icond cond args s1 s2)
  | Ireturn val, nil => Some (RTL.Ireturn val)
  | Isel ty c r1 r2 dst, s::nil => Some (RTL.Iop (Osel (Cmasknotzero Int.one) ty) (r1::r2::c::nil) dst s)
  | _, _ => None
  end.

Definition option_join {A}: option (option A) -> option A := fun a => match a with
  | Some a => a
  | None => None end.

Definition convert_vertex (f: SelRTL.function) (v': positive) (i: instruction): option RTL.instruction :=
  let v := Pos_to_pred_nat v' in
  let succs := map Pos.of_succ_nat (successors f.(g) v) in
  convert_instruction succs i.

Definition convert_graph_to_rtl (f: SelRTL.function) : res RTL.code :=
  let t := PTree.map (convert_vertex f) f.(code) in
  if PTree_Properties.for_all t (fun _ i => match i with None => false | _ => true end) then
    OK (PTree.combine (fun a _ => option_join a) t (PTree.empty (option nat)))
  else
    Error (msg "#successors is invalid for some instruction(s)").

Program Definition transl_function (f: SelRTL.function): res RTL.function :=
  match convert_graph_to_rtl f with
  | Error a => Error a
  | OK code =>
    OK (RTL.mkfunction f.(sig) f.(params) f.(stacksize) f.(taint_attr) code (Pos.of_succ_nat f.(entry)))
  end.

Definition transl_fundef := transf_partial_fundef transl_function.
Definition transf_program (p: SelRTL.program) : res RTL.program := transform_partial_program transl_fundef p.


(*** SEMANTIC MATCH AND PRESERVATION ***)

Inductive match_states: SelRTL.state -> RTL.state -> Prop :=
  | match_state:
      forall f tf sp pc rs rs' m wt
        (TF: transl_function f = OK tf)
        (LD: regs_lessdef rs rs')
        (WT: wt_regset f.(env) rs'),
      match_states (SelRTL.State f sp pc rs m wt) (RTL.State nil tf sp (Pos.of_succ_nat pc) rs' m)
  | match_initstate:
      forall args f tf m wt def
        (TF: transl_fundef f = OK tf),
        match_states (SelRTL.InitState f args m wt def) (RTL.Callstate nil tf args m)
  | match_endstate:
      forall f v v' m
      (LD: Val.lessdef v v'),
      match_states (SelRTL.EndState f v m) (RTL.Returnstate nil v' m).

Definition match_prog (p: SelRTL.program) (tp: RTL.program) :=
  match_program (fun cu f tf => transl_fundef f = OK tf) eq p tp.

Lemma transf_program_match: forall p tp, transf_program p = OK tp -> match_prog p tp.
Proof.
  intros. now apply match_transform_partial_program.
Qed.

Section Preservation.

Variable prog: SelRTL.program.
Variable tprog: RTL.program.
Hypothesis TRANSL: match_prog prog tprog.

Let ge : SelRTL.genv := Genv.globalenv prog.
Let tge : RTL.genv := Genv.globalenv tprog.

(* Trivial boilerplate *)

Lemma symbols_preserved:
  forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
Proof (Genv.find_symbol_transf_partial TRANSL).

Lemma senv_preserved:
  Senv.equiv (Genv.to_senv ge) (Genv.to_senv tge).
Proof (Genv.senv_transf_partial TRANSL).

Lemma function_ptr_translated:
  forall (b: block) (f: SelRTL.fundef),
  Genv.find_funct_ptr ge b = Some f ->
  exists tf,
  Genv.find_funct_ptr tge b = Some tf /\ transl_fundef f = OK tf.
Proof (Genv.find_funct_ptr_transf_partial TRANSL).

Lemma sig_function_translated:
  forall f tf,
  transl_fundef f = OK tf ->
  RTL.funsig tf = SelRTL.funsig f.
Proof.
  intros. unfold SelRTL.funsig, RTL.funsig.
  unfold transl_fundef, transf_partial_fundef, bind, transl_function in H.
  destruct tf eqn:TF; destruct f eqn:F; try congruence; case convert_graph_to_rtl in H; try congruence.
  injection H; intro; now subst.
Qed.

(* Initial and final states and step *)

Lemma transl_initial_states:
  forall S, SelRTL.initial_state prog S ->
  exists R, RTL.initial_state tprog R /\ match_states S R.
Proof.
  intros. inv H.
  exploit function_ptr_translated. eauto. intros [tf [G T]].
  exists (RTL.Callstate nil tf nil m0). split.
    econstructor.
  - now apply (Genv.init_mem_transf_partial TRANSL).
  - replace (prog_main tprog) with (prog_main prog). rewrite symbols_preserved. eauto.
    symmetry. eapply match_program_main. eauto.
  - exact G.
  - rewrite <- FS. now apply sig_function_translated.
  - now constructor.
Qed.

Lemma transl_final_states:
  forall S R r,
  match_states S R -> SelRTL.final_state S r -> RTL.final_state R r.
Proof.
  intros. inv H0. inv H. inv LD. constructor.
Qed.


Ltac unfold_tf T := unfold transl_function in T; let C := fresh in case convert_graph_to_rtl eqn:C in T; try congruence; injection T; clear T; let X := fresh in intro X; rewrite <- X in *.

Lemma transfstep': forall f tf pc i s,
  getinstr f pc = Some i ->
  successors f.(g) pc = s ->
  transl_function f = OK tf ->
  tf.(fn_code) @! pc = convert_instruction (map Pos.of_succ_nat s) i.
Proof.
  intros. unfold_tf H1.
  unfold convert_graph_to_rtl in H2; case PTree_Properties.for_all in H2; try congruence; injection H2; clear H2; intro; subst.
  unfold fn_code. rewrite PTree.gcombine. 2: auto. rewrite PTree.gmap. unfold Coqlib.option_map.
  unfold convert_vertex. replace (Pos_to_pred_nat (Pos.of_succ_nat pc)) with pc. 2: symmetry; apply predsucc.
  unfold getinstr in H. now rewrite H.
Qed.

Ltac transfstep :=
  match goal with
  | [ H1: getinstr ?f ?pc = Some ?i, H2: uniquesucc ?f ?pc = Some ?pc', H3: transl_function ?f = OK ?tf
    |- ?tf.(fn_code) @! ?pc = Some ?i' ] =>
      erewrite transfstep' with (f:=f) (s:=pc'::nil); eauto;
      unfold convert_instruction; simpl; eauto; transfstep
  | [ U: uniquesucc ?f ?pc = Some ?pc' |- successors (g ?f) ?pc = ?pc' :: nil ] =>
      unfold uniquesucc in U; case successors eqn:S1 in U; try congruence; match type of U with (match ?S with _ => _ end = _) => case S eqn:S2 in U end; congruence
  | [ |- match_states ?a ?b ] => econstructor; eauto
  end. 


Theorem transl_step_correct:
  forall s1 t s2, SelRTL.step ge s1 t s2 ->
  forall ts1 (MS: match_states s1 ts1),
  exists ts2, RTL.step tge ts1 t ts2 /\ match_states s2 ts2.
Proof.
  intros. inv MS.
  + inv H.
  * econstructor; split. constructor. transfstep. transfstep.
  * (* operation also evals on the more-defined registers to something more-defined *)
    copy OP. erewrite eval_operation_preserved in OP0. eapply eval_operation_lessdef with (m2:=m) (vl2:=rs'##args) in OP0 as [v' []].
    2: now apply regs_lessdef_regs. 2: apply Mem.extends_refl. 2: symmetry; apply symbols_preserved.
    (* now construct the state *)
    econstructor; split. econstructor 2; eauto.
    transfstep. transfstep. now apply set_reg_lessdef. apply wt_regset_assign; auto.
    destruct f.(WELLTYPED). apply wt_instrs in I. inv I.
    { simpl in H. injection H; intro. rewrite <- H1, H2. now apply WT. }
    { apply type_of_operation_sound in H; auto. now rewrite <- H6 in H. }
  * copy AD. erewrite eval_addressing_preserved in AD0. eapply eval_addressing_lessdef in AD0 as [a' []].
    2: now apply regs_lessdef_regs. 2: symmetry; apply symbols_preserved.
    eapply Mem.loadv_extends in MEM as [val' []]. 2: apply Mem.extends_refl. 2: apply H0.
    econstructor; split. econstructor 3; eauto.
    transfstep; auto. transfstep. now apply set_reg_lessdef. apply wt_regset_assign; auto.
    destruct f.(WELLTYPED). apply wt_instrs in I. inv I.
    apply type_of_addressing_sound in H; auto.
    case a' eqn:?; try inv H1. apply Mem.load_type in H4. now rewrite <- H8 in H4.
  * (* condition also evals on the more-defined registers to something more-defined *)
    eapply eval_condition_lessdef with (m2:=m) (vl2:=rs'##args) in H9.
    2: now apply regs_lessdef_regs. 2: apply Mem.extends_refl.
    (* now construct the state *)
    econstructor; split. econstructor 8.
    erewrite transfstep' with (f:=f) (s:=ifso::ifnot::nil) (i:=Icond cond args); eauto. unfold convert_instruction; simpl; eauto. eauto. eauto.
    case b; transfstep.
  * econstructor; split. econstructor 2. erewrite transfstep' with (f:=f) (i:=(Isel ty sel r1 r2 res)) (s:=pc'::nil). unfold getinstr in I. unfold convert_instruction. simpl. auto.
    auto. transfstep. auto.
    Unshelve. 3: { exact (eval_sel sel r1 r2 rs' ty). }
    simpl. unfold eval_sel, Val.select, Coqlib.option_map, Val.maskzero_bool.
    auto. transfstep.
    apply set_reg_lessdef; auto. apply eval_sel_lessdef; auto.
    enough (env f res = ty).
    { apply wt_regset_assign; auto. rewrite H. unfold eval_sel. unfold Val.select. case Coqlib.option_map; [intro; apply Val.normalize_type | constructor]. }
    { destruct f.(WELLTYPED). apply wt_instrs in I. now inv I. }
  * econstructor; split. econstructor 10.
    erewrite transfstep' with (f:=f) (s:=nil) (i:=Ireturn or); auto. unfold convert_instruction. now simpl.
    unfold_tf TF. unfold fn_stacksize. eauto.
    constructor. case or; easy.
  + inv H.
  * unfold transl_fundef, transf_partial_fundef, bind in TF; case transl_function eqn:TF' in TF; try congruence. injection TF; intro; subst.
    econstructor. split.
    econstructor 11.
    copy TF'.
    unfold_tf TF'. unfold fn_stacksize. eauto.
    copy TF'.
    unfold_tf TF'. unfold fn_entrypoint, fn_params.
    econstructor 1. auto. apply regs_lessdef_refl. apply RTLtyping.wt_init_regs. destruct f0.(WELLTYPED). now rewrite wt_params.
  * unfold transl_fundef, transf_partial_fundef, bind in TF. injection TF; intro; subst.
    econstructor. split.
    constructor. eapply external_call_symbols_preserved. apply senv_preserved. eauto.
    transfstep.
  + inv H.
Qed.

Theorem transf_program_correct:
  forward_simulation (SelRTL.semantics prog) (RTL.semantics tprog).
Proof.
  eapply forward_simulation_step.
  apply senv_preserved.
  exact transl_initial_states.
  exact transl_final_states.
  exact transl_step_correct.
Qed.

End Preservation.