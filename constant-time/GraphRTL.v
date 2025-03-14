Require Import Common Coqlib Classical Datatypes.
Require Import AST RTL Memory Registers Maps Values Events Globalenvs Smallstep Op Integers.
Require Import Graph GraphDual.
Require Import Smallstep Errors.
Require Import ListsExtra Before Permutation.
Require Import TaintAnalysis SharedTypes SafeOp SafeOpProof.
Require Import MemAxiom.
Require Import Coq.Program.Equality.

(* We require an GraphRTL to be acyclic and therefore have a topological sort. *)

Record function : Type := mkfunction {
  code: PTree.t instruction;
  sig: signature;
  params: list reg;
  stacksize: Z;
  g: G;
  entry: nat;
  exit: nat;
  n: nat;
  
  idx: list nat;
  IDX: top_sort g idx;

  N: n > 0;
  N_MAX: n < Z.to_nat Int.modulus;
  VS: g.(vs) = seq 0 n;
  NCODE: forall pc, code @! pc <> None <-> pc < n;
  SUCCS: forall pc i, code @! pc = Some i -> length (successors g pc) = num_successors i;
  ENTRY: vertex g entry;
  EXIT: forall v, v = exit <-> is_exit g v;

  taint_attr: fun_taint_attr reg;
  taint_f := (TaintAnalysis.Build_taint_func code taint_attr g exit n idx IDX N VS NCODE EXIT);
  TAINT_RES: { res : PMap.t DS.L.t | TaintAnalysis.res taint_f = Some res };
  uniform_cond: V -> bool;
  UNIFORM: uniform_cond = TaintAnalysis.uniform_cond taint_f TAINT_RES;

  SAFE: forall pc i, code @! pc = Some i -> instr_safe i;
  UNI_MEM: forall pc c a ar d, code @! pc = Some (Iload c a ar d) -> uni taint_f TAINT_RES pc;

  env: regenv;
  ANYFREE: any_free_regenv env (max_reg_function code params);
  WELLTYPED: wt_function env code params sig;
}.

Definition fundef := AST.fundef function.
Definition program := AST.program fundef unit.

Definition funsig (fd: fundef) :=
  match fd with
  | Internal f => sig f
  | External ef => ef_sig ef
  end.

Section Semantics.

(* Abbreviations *)
Definition getinstr f n := f.(code) @! n.
Definition uniquesucc f n := match (successors f.(g) n) with x::nil => Some x | _ => None end.

Definition genv := Genv.t fundef unit.
Definition regset := Regmap.t val.

Variable ge: genv.

(*** WELLTYPEDNESS ***)

Definition def_regset f := def_regset (max_reg_function f.(code) f.(params)).

Lemma wt_instr_in_function: forall f pc instr,
  getinstr f pc = Some instr ->
  wt_instr f.(env) f.(sig) instr.
Proof.
  intros. destruct f.(WELLTYPED). enow eapply wt_instrs.
Qed.

Lemma max_reg_transl: forall f pc instr,
  getinstr f pc = Some instr ->
  (forall r, In r (instr_uses instr) -> Ple r (max_reg_function f.(code) f.(params))).
Proof.
  intros. enow eapply max_reg_function_use.
Qed.

Lemma op_is_safe: forall f pc op args res,
  getinstr f pc = Some (Iop op args res) ->
  op_safe op.
Proof.
  intros. now pose proof (f.(SAFE) pc (Iop op args res) H).
Qed.

Lemma op_step_def: forall f sp pc rs m op args res pc' v
      (I: getinstr f pc = Some(Iop op args res))
      (U: uniquesucc f pc = Some pc')
      (OP: eval_operation ge sp op rs##args m = Some v)
      (SP: exists b ofs, sp = Vptr b ofs),
      wt_regset f.(env) rs ->
      def_regset f rs ->
      def_regset f (rs#res <- v).
Proof.
  intros.
  eapply def_exec_Iop; eauto.
  * enow eapply op_is_safe.
  * intros; enow eapply max_reg_transl.
  * enow eapply max_reg_function_def.
  * enow eapply wt_instr_in_function.
Qed.


Lemma load_step_def: forall f pc rs m chunk addr args a dst v
      (I: getinstr f pc = Some(Iload chunk addr args dst))
      (MEM: Mem.loadv chunk m a = Some v),
      def_regset f rs ->
      def_regset f (rs#dst <- v).
Proof.
  intros.
  eapply max_reg_function_def in I. 2: easy.
  apply def_regset_assign; eauto. now apply mem_load_always_defined in MEM.
Qed.


(*** STATE + STEP ***)


Inductive state : Type :=
  | State: forall (f: function)
                  (sp: val)
                  (pc: nat)
                  (rs: regset)
                  (m: mem)
                  (WT: wt_regset f.(env) rs)
                  (DEF: def_regset f rs),
           state
  | InitState: forall (f: fundef)
                      (args: list val)
                      (m: mem)
                      (VL: Val.has_type_list args (sig_args (funsig f)))
                      (DEF: def_args args),
               state
  | EndState: forall (f: fundef)
                     (v: val)
                     (m: mem),
              state.


Inductive step: state -> Events.trace -> state -> Prop :=
  | exec_Inop:
      forall f sp pc rs m pc' wt def,
      getinstr f pc = Some(Inop) ->
      uniquesucc f pc = Some pc' ->
      step (State f sp pc rs m wt def)
        E0 (State f sp pc' rs m wt def)
  | exec_Iop:
      forall f sp pc rs m op args res pc' v wt def
      (I: getinstr f pc = Some(Iop op args res))
      (U: uniquesucc f pc = Some pc')
      (OP: eval_operation ge sp op rs##args m = Some v)
      (SP: exists b ofs, sp = Vptr b ofs),
      step (State f sp pc rs m wt def)
        E0 (State f sp pc' (rs#res <- v) m
            ltac:(eapply wt_exec_Iop; eauto; enow eapply wt_instr_in_function)
            ltac:(enow eapply op_step_def))
  | exec_Iload:
      forall f sp pc rs m chunk addr args dst pc' a v wt def
      (I: getinstr f pc = Some(Iload chunk addr args dst))
      (U: uniquesucc f pc = Some pc')
      (AD: eval_addressing ge sp addr rs##args = Some a)
      (MEM: Mem.loadv chunk m a = Some v),
      step (State f sp pc rs m wt def)
        E0 (State f sp pc' (rs#dst <- v) m
            ltac:(eapply wt_exec_Iload; eauto; enow eapply wt_instr_in_function)
            ltac:(enow eapply load_step_def))
  | exec_Icond:
      forall f sp pc rs m cond args ifso ifnot b pc' wt def,
      getinstr f pc = Some(Icond cond args) ->
      successors f.(g) pc = ifso::ifnot::nil ->
      eval_condition cond rs##args m = Some b ->
      pc' = (if b then ifso else ifnot) ->
      step (State f sp pc rs m wt def)
        E0 (State f sp pc' rs m wt def)
  | exec_function_internal:
      forall f args m m' stk wt def,
      Mem.alloc m 0 f.(stacksize) = (m', stk) ->
      step (InitState (Internal f) args m wt def)
        E0 (State f
                  (Vptr stk Ptrofs.zero)
                  f.(entry)
                  (init_all_regs f.(env) f.(code) f.(params) args)
                  m'
                  ltac:(eapply init_all_regs_wt; eauto; now destruct f.(WELLTYPED))
                  ltac:(eapply init_all_regs_def))
  | exec_function_external:
      forall f args res t m m' wt def,
      external_call f ge args m t res m' ->
      step (InitState (External f) args m wt def)
         t (EndState (External f) res m')
  | exec_Ireturn:
      forall f stk pc rs m or m' wt def,
      getinstr f pc = Some(Ireturn or) ->
      successors f.(g) pc = nil ->
      Mem.free m stk 0 f.(stacksize) = Some m' ->
      step (State f (Vptr stk Ptrofs.zero) pc rs m wt def)
        E0 (EndState (Internal f) (regmap_optget or Vundef rs) m').

End Semantics.

Lemma wt_initial_state: forall f,
  funsig f = signature_main ->
  Val.has_type_list nil (sig_args (funsig f)).
Proof.
  intros. now rewrite H.
Qed.

Inductive initial_state (p: program): state -> Prop :=
  | initial_state_intro: forall b f m0
      (FS: funsig f = signature_main),
      let ge := Genv.globalenv p in
      Genv.init_mem p = Some m0 ->
      Genv.find_symbol ge p.(prog_main) = Some b ->
      Genv.find_funct_ptr ge b = Some f ->
      initial_state p (InitState f nil m0 ltac:(now apply wt_initial_state) ltac:(easy)).

Inductive final_state: state -> int -> Prop :=
  | final_state_intro: forall f r m,
      final_state (EndState f (Vint r) m) r.

Definition semantics (p: program) :=
  Semantics step (initial_state p) final_state (Genv.globalenv p).


(* Facts about the underlying graph *)

Section GraphProperties.

Lemma vertex_n: forall f x,
  vertex f.(g) x <-> x < f.(n).
Proof.
  intros. unfold vertex. rewrite f.(VS), in_seq. lia.
Qed.

Lemma getinstr_vertex: forall f pc i,
  getinstr f pc = Some i -> vertex f.(g) pc.
Proof.
  intros. unfold getinstr in H. assert ((code f) @! pc <> None) by congruence.
   apply f.(NCODE) in H0. unfold vertex. rewrite f.(VS). apply in_seq. lia.
Qed.

Lemma uniquesucc_edge:
  forall f pc pc' i, 
  getinstr f pc = Some i ->
  uniquesucc f pc = Some pc' ->
  pc → pc' in f.(g).
Proof.
  intros. unfold uniquesucc in H0. case successors eqn:A in H0; try congruence. case l eqn:B in H0; try congruence.
  injection H0. intro. subst.
  apply getinstr_vertex in H. apply successors_spec with (w:=pc') in H. apply H. rewrite A. apply in_eq.
Qed.

Lemma return_exit: forall f v,
  v = f.(exit) <-> exists o, (code f) @! v = Some (Ireturn o).
Proof.
  intros. split; intro.
  * apply f.(EXIT) in H as [].
    case (f.(code) @! v) eqn:?; [|now apply f.(NCODE) in Heqo; [|apply vertex_n]].
    case i eqn:?; apply f.(SUCCS) in Heqo; rewrite H0 in Heqo; simpl in *; try lia. now exists o.
  * destruct H. apply f.(EXIT). split. enow eapply getinstr_vertex. apply f.(SUCCS) in H. simpl in H. case successors in *. auto. simpl in H. lia.
Qed.

(* Any valid step corresponds to an edge in the graph *)
Theorem step_is_edge: forall ge t f sp sp' pc pc' rs rs' m m' wt wt' def def',
  step ge (State f sp pc rs m wt def) t (State f sp' pc' rs' m' wt' def') ->
  pc → pc' in f.(g).
Proof.
  intros. dependent destruction H.
  1-3: eapply uniquesucc_edge; eauto.
  apply getinstr_vertex in H. apply successors_spec with (w := if b then ifso else ifnot) in H. apply H. rewrite H0.
  case b; [|apply in_cons]; apply in_eq.
Qed.

(* Facts about topological sorts on an GraphRTL. *)

Lemma top_sort_len: forall f, length f.(idx) = f.(n).
Proof.
  intros. destruct f.(IDX). now rewrite Permutation_length with (l':=f.(g).(vs)), f.(VS), seq_length.
Qed.

Lemma rtl_top_sort_exit: forall f d,
  f.(exit) = nth (f.(n) - 1) f.(idx) d.
Proof.
  intros. pose f.(IDX) as H. apply top_sort_last_exit with (d:=d) in H.
  * apply f.(EXIT) in H; pose f.(VS). now rewrite e, seq_length in H.
  * pose f.(N); pose f.(VS). now rewrite e, seq_length.
Qed.

Lemma rtl_top_sort_exit_before: forall f v,
  ~ f.(exit) << v in f.(idx).
Proof.
  intros. intro.
  pose proof (rtl_top_sort_exit f). destruct H as [i [j [? [e e0]]]].
  assert (i = f.(n)-1).
  { assert (f.(n)-1 < length f.(idx)) by (rewrite top_sort_len with (f:=f); pose f.(N); auto; lia).
    eapply nth_or_error in H1. erewrite <- H0, <- e in H1. apply NoDup_nth_error in H1; auto. apply top_sort_nodup with (g:=f.(g)), f.(IDX). now apply nth_error_len in e. }
  apply nth_error_len in e0. rewrite top_sort_len with (f:=f) in e0; auto. lia.
  Unshelve. exact 0.
Qed.

End GraphProperties.