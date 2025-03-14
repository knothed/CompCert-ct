Require Import Common Coqlib Classical Datatypes.
Require Import AST Memory Registers Maps Values Events Globalenvs Smallstep Op Integers.
Require Import Smallstep Errors.
Require Import ListsExtra Before Permutation GraphRTL.
Require Import Graph GraphDual InfluenceRegion.
Require Import SharedTypes SafeOp SafeOpProof TaintAnalysis.
Require Import MemAxiom.
Require Import Coq.Program.Equality.

Definition chain_inv g uniform_cond exit EXIT idx IDX v w :=
  exists cv cw cs, (forall c, In c (cv::cw::cs) -> uniform_cond c = false) /\ in_ir g exit EXIT idx IDX cv v /\
    in_ir g exit EXIT idx IDX cw w /\ chain_via g exit EXIT idx IDX cs cv cw.

Record function : Type := mkfunction {
  code: PTree.t instruction;
  sig: signature;
  params: list reg;
  stacksize: Z;
  g: G; (* result of hack-moll *)
  entry: nat;
  exit: nat;
  n: nat;

  uniform_cond: nat -> bool;

  (* g_pred is the original graph. There is a mapping from edges v->w in g_pred to edges v->w' in g. *)
  g_pred: G;
  detour: V -> V -> V;
  DETOUR_SPEC: forall v w, v → w in g_pred -> v → (detour v w) in g /\ postdom g exit w (detour v w);
  DETOUR_COND_UNIFORM: forall v c a, code @! v = Some (Icond c a) -> uniform_cond v = true -> successors g v = map (detour v) (successors g_pred v);
  idx: list V;
  top_sort_g: top_sort g idx;
  top_sort_pred: top_sort g_pred idx;

  N: n > 0;
  N_MAX: n < Z.to_nat Int.modulus;
  VS: g.(vs) = seq 0 n;
  NCODE: forall pc, code @! pc <> None <-> pc < n;
  SUCCS_PRED: forall pc i, code @! pc = Some i -> length (successors g_pred pc) = num_successors i;
  SUCCS_G: forall pc i, code @! pc = Some i -> min_successors i <= length (successors g pc) <= num_successors i;
  SUCCS_COND: forall pc c args, code @! pc = Some (Icond c args) -> uniform_cond pc = false <-> length (successors g pc) = 1;
  ENTRY: vertex g entry;
  EXIT: forall v, v = exit <-> is_exit g v;
  EXIT': forall v, v = exit <-> is_exit g_pred v;
  PRED: g_pred.(vs) = g.(vs);

  DETOUR_CHAIN: forall v w, v → w in g_pred -> w <> detour v w -> chain_inv g_pred uniform_cond exit EXIT' idx top_sort_pred w (detour v w);

  (* Taint ana of original graph *)
  taint_attr: fun_taint_attr reg;
  taint_f := (TaintAnalysis.Build_taint_func code taint_attr g_pred exit n idx top_sort_pred N ltac:(rewrite PRED; apply VS) NCODE EXIT');
  TAINT_RES: { res : PMap.t DS.L.t | TaintAnalysis.res taint_f = Some res };
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

Definition genv := Genv.t fundef unit.
Definition regset := Regmap.t val.

Variable ge: genv.

Notation "v ▷ w 'in' f" := (postdom f.(g) f.(exit) w v) (at level 49).

Notation "v → ( w , w' ) 'in' f" := (v → w' in f.(g_pred) /\ f.(detour) v w' = w) (at level 49).

Lemma target_reverse: forall f v w w',
  v → (w, w') in f -> v → w in f.(g).
Proof.
  intros. destruct H. apply f.(DETOUR_SPEC) in H. now subst.
Qed.

Definition getinstr f n := f.(code) @! n.

(* Unique successor of n in (g, g_pred). *)
Definition uniquesucc f n := match (successors f.(g_pred) n) with x::nil => Some (f.(detour) n x, x) | _ => None end.

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

Inductive state : Type :=
  | State: forall (f: function)
                  (sp: val)
                  (v: nat)
                  (rs: regset)
                  (m: mem)
                  (v_target: nat) (* Until hitting v_target, operations are dummy-executed *)
                  (pd: v ▷ v_target in f)
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

Lemma vertex_n: forall f x,
  vertex f.(g) x <-> x < f.(n).
Proof.
  intros. unfold vertex. rewrite f.(VS), in_seq. lia.
Qed.

Lemma vertex_same: forall f v,
  vertex f.(g) v <-> vertex f.(g_pred) v.
Proof.
  intro. unfold vertex. rewrite f.(PRED). easy.
Qed.

Lemma getinstr_vertex: forall f pc i,
  getinstr f pc = Some i -> vertex f.(g) pc.
Proof.
  intros. unfold getinstr in H. assert ((code f) @! pc <> None) by congruence.
  apply f.(NCODE) in H0. unfold vertex. rewrite f.(VS). apply in_seq. lia.
Qed.

Lemma return_exit: forall f v,
  v = f.(exit) <-> exists o, (code f) @! v = Some (Ireturn o).
Proof.
  intros. split; intro.
  * apply f.(EXIT) in H as [].
    case (f.(code) @! v) eqn:?; [|now apply f.(NCODE) in Heqo; [|apply vertex_n]].
    case i eqn:?; apply f.(SUCCS_G) in Heqo; rewrite H0 in Heqo; simpl in *; try lia. now exists o.
  * destruct H. apply f.(EXIT). split. enow eapply getinstr_vertex. apply f.(SUCCS_G) in H. simpl in H. case successors in *. auto. simpl in H. lia.
Qed.

Lemma uniquesucc_edge_full: forall f v w w' i, 
  getinstr f v = Some i ->
  uniquesucc f v = Some (w, w') ->
  v → w' in f.(g_pred) /\ v → w in f.(g) /\ w ▷ w' in f.
Proof.
  intros. unfold uniquesucc in H0. case successors eqn:A in H0; try congruence. case l eqn:B in H0; try congruence.
  injection H0. intros. subst.
  split; [|split].
  2-3: apply f.(DETOUR_SPEC).
  all: apply successors_spec; [ apply vertex_same; now apply getinstr_vertex in H | rewrite A; apply in_eq ].
Qed.

Lemma succ_not_exit: forall f v w' o,
  successors (g_pred f) v = w' :: nil ->
  getinstr f v <> Some (Ireturn o).
Proof.
  intros. intro. assert (exists o, f.(code) @! v = Some (Ireturn o)) by now exists o.
  apply return_exit in H1. apply f.(EXIT) in H1 as [].
  assert (v → w' in f.(g_pred)). apply successors_spec. apply vertex_same. auto. rewrite H. apply in_eq.
  apply f.(DETOUR_SPEC) in H3 as []. apply successors_spec in H3; auto. rewrite H2 in H3. easy.
Qed.

Lemma uniquesucc_edge_succs_full: forall f v w w' i,
  getinstr f v = Some i ->
  uniquesucc f v = Some (w, w') ->
  successors f.(g_pred) v = w'::nil /\ successors f.(g) v = w::nil.
Proof.
  intros. copy H. apply getinstr_vertex in H1.
  unfold uniquesucc in H0. case successors eqn:A in H0; try congruence. case l eqn:B in H0; try congruence.
  injection H0. intros. subst.
  split; auto.
  copy H. apply f.(SUCCS_G) in H. case (successors f.(g) v) eqn:?.
  case i eqn:?; simpl in H; try lia. exfalso. enow eapply succ_not_exit.
  case l eqn:?; simpl in H; try lia.
  * f_equal.
    assert (v → w' in f.(g_pred)). apply successors_spec. apply vertex_same. auto. rewrite A. apply in_eq.
    apply f.(DETOUR_SPEC) in H3 as []. apply successors_spec in H3. rewrite Heql in H3. now case H3. auto.
  * case i eqn:?; simpl in H; try lia. apply f.(SUCCS_PRED) in H2. rewrite A in H2. easy.
Qed.

Lemma cond_edge_full: forall f v w (b: bool) ifso ifnot i,
  getinstr f v = Some i ->
  successors f.(g_pred) v = ifso::ifnot::nil ->
  let w' := (if b then ifso else ifnot) in
  w = f.(detour) v w' ->
  v → w' in f.(g_pred) /\ v → w in f.(g) /\ w ▷ w' in f.
Proof.
  intros. subst.
  split; [|split].
  2-3: apply f.(DETOUR_SPEC).
  all: apply successors_spec; unfold w'; [ apply vertex_same; now apply getinstr_vertex in H |]; rewrite H0; case b; [|apply in_cons]; apply in_eq.
Qed.

Lemma cond_num_successors: forall f v cond args,
  getinstr f v = Some (Icond cond args) ->
  length (successors f.(g) v) = if f.(uniform_cond) v then 2 else 1.
Proof.
  intros. copy H. apply SUCCS_G in H. apply SUCCS_COND in H0.
  simpl in *. case (f.(uniform_cond) v) in *; lia.
Qed.

Lemma uniquesucc_edge_g: forall f v w w' i, 
  getinstr f v = Some i ->
  uniquesucc f v = Some (w, w') ->
  v → w in f.(g).
Proof.
  apply uniquesucc_edge_full.
Qed.

Lemma uniquesucc_edge_pred: forall f v w w' i, 
  getinstr f v = Some i ->
  uniquesucc f v = Some (w, w') ->
  v → w' in f.(g_pred).
Proof.
  apply uniquesucc_edge_full.
Qed.

Lemma postdom_kept_simple: forall f v v_targ w w' i, 
  getinstr f v = Some i ->
  uniquesucc f v = Some (w, w') ->
  v <> v_targ ->
  v ▷ v_targ in f ->
  w ▷ v_targ in f.
Proof.
  intros. enow eapply postdom_edge; [ apply f.(EXIT) | | eapply uniquesucc_edge_g | ].
Qed.

Lemma postdom_kept_cond: forall f v v_targ (b:bool) ifso ifnot w w' i, 
  getinstr f v = Some i ->
  successors f.(g_pred) v = ifso::ifnot::nil ->
  w' = (if b then ifso else ifnot) ->
  w = f.(detour) v w' ->
  v <> v_targ ->
  v ▷ v_targ in f ->
  w ▷ v_targ in f.
Proof.
  intros. enow eapply postdom_edge; [ apply f.(EXIT) | | eapply cond_edge_full; eauto; rewrite <- H1 | ].
Qed.

Lemma postdom_refl_entry:
  forall f,
  f.(entry) ▷ f.(entry) in f.
Proof.
  intros. now apply postdom_refl; [apply f.(EXIT) | apply f.(ENTRY)].
Qed.

Lemma args_params_same_length: forall f args,
  Val.has_type_list args (sig_args f.(sig)) ->
  length (f.(params)) = length args.
Proof.
  intros. destruct f.(WELLTYPED).
  remember (sig_args f.(sig)) as SIG.
  replace (length f.(params)) with (length SIG) by (rewrite <- wt_params; apply map_length).
  clear HeqSIG. clear wt_params. generalize dependent SIG. induction args.
  * now case SIG in *.
  * case SIG in *. easy. intros. inv H. simpl. apply IHargs in H1. lia. 
Qed.

Inductive step: state -> Events.trace -> state -> Prop :=
  | do_nothing:
      forall f sp v v_targ w w' i rs m PD PD' wt def
      (I: getinstr f v = Some i)
      (U: uniquesucc f v = Some (w, w'))
      (N: v <> v_targ),
      step (State f sp v rs m v_targ PD wt def)
        E0 (State f sp w rs m v_targ PD' wt def)
  | do_nothing_cond:
      forall f sp v v_targ cond args (b: bool) ifso ifnot w' rs m PD PD' wt def
      (I: getinstr f v = Some(Icond cond args))
      (S: successors f.(g_pred) v = ifso::ifnot::nil)
      (N: v <> v_targ)
      (B: w' = (if b then ifso else ifnot)),
      let w := f.(detour) v w' in
      eval_condition cond rs##args m = Some b ->  (* condition wird trotzdem ausgewertet, ist aber ohne side-effects!! *)
      step (State f sp v rs m v_targ PD wt def)
        E0 (State f sp w rs m v_targ PD' wt def)

  | exec_Inop:
      forall f sp v rs m w w' PD PD' wt def
      (I: getinstr f v = Some(Inop))
      (U: uniquesucc f v = Some (w, w')),
      step (State f sp v rs m v PD wt def)
        E0 (State f sp w rs m w' PD' wt def)
  | exec_Iop:
      forall f sp v rs m op args res w w' r PD PD' wt def
      (I: getinstr f v = Some(Iop op args res))
      (U: uniquesucc f v = Some (w, w'))
      (OP: eval_operation ge sp op rs##args m = Some r)
      (SP: exists b ofs, sp = Vptr b ofs),
      step (State f sp v rs m v PD wt def)
        E0 (State f sp w (rs#res <- r) m w' PD'
            ltac:(eapply wt_exec_Iop; eauto; enow eapply wt_instr_in_function)
            ltac:(enow eapply op_step_def))
  | exec_Iload:
      forall f sp v w w' rs m chunk addr args dst a val wt def PD PD'
      (I: getinstr f v = Some(Iload chunk addr args dst))
      (U: uniquesucc f v = Some (w, w'))
      (AD: eval_addressing ge sp addr rs##args = Some a)
      (MEM: Mem.loadv chunk m a = Some val),
      step (State f sp v rs m v PD wt def)
        E0 (State f sp w (rs#dst <- val) m w' PD'
            ltac:(eapply wt_exec_Iload; eauto; enow eapply wt_instr_in_function)
            ltac:(enow eapply load_step_def))
  | exec_Icond:
      forall f sp v rs m cond args ifso ifnot (b: bool) w' PD PD' wt def
      (I: getinstr f v = Some(Icond cond args))
      (S: successors f.(g_pred) v = ifso::ifnot::nil)
      (B: w' = (if b then ifso else ifnot)),
      let w := f.(detour) v w' in
      eval_condition cond rs##args m = Some b ->
      step (State f sp v rs m v PD wt def)
        E0 (State f sp w rs m w' PD' wt def)
  | exec_function_internal:
      forall f args m m' stk wt def,
      Mem.alloc m 0 f.(stacksize) = (m', stk) ->
      step (InitState (Internal f) args m wt def)
        E0 (State f
                  (Vptr stk Ptrofs.zero)
                  f.(entry)
                  (init_all_regs f.(env) f.(code) f.(params) args)
                  m'
                  f.(entry)
                  ltac:(enow eapply postdom_refl_entry)
                  ltac:(eapply init_all_regs_wt; eauto; now destruct f.(WELLTYPED))
                  ltac:(eapply init_all_regs_def))
  | exec_function_external:
      forall f args res t m m' wt def,
      external_call f ge args m t res m' ->
      step (InitState (External f) args m wt def)
         t (EndState (External f) res m')
  | exec_Ireturn:
      forall f stk v rs m or m' PD wt def,
      getinstr f v = Some(Ireturn or) ->
      successors f.(g) v = nil ->
      Mem.free m stk 0 f.(stacksize) = Some m' ->
      step (State f (Vptr stk Ptrofs.zero) v rs m v PD wt def)
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

Inductive state_emergent (p: program) (s: state): Prop :=
  | state_emergent_intro: forall init t,
    initial_state p init -> star step (Genv.globalenv p) init t s -> state_emergent p s. 

Lemma state_emergent_init: forall p i,
  initial_state p i -> state_emergent p i.
Proof.
  intros. econstructor; eauto. constructor.
Qed.

Lemma state_emergent_step: forall p s1 t s2,
  step (Genv.globalenv p) s1 t s2 -> state_emergent p s1 -> state_emergent p s2.
Proof.
  intros. inv H0. econstructor; eauto. eapply star_right; eauto.
Qed.

Lemma state_emergent_plus: forall p s1 t s2,
  plus step (Genv.globalenv p) s1 t s2 -> state_emergent p s1 -> state_emergent p s2.
Proof.
  intros. inv H0. inv H. econstructor; eauto.
  eapply star_trans with (s2:=s1); eauto. enow econstructor.
Qed.


Definition semantics (p: program) :=
  Semantics step (initial_state p) final_state (Genv.globalenv p).

Lemma step_is_edge:
  forall ge f v w sp sp' rs rs' m m' vtarg wtarg pd pd' e wt wt' def def',
  step ge (State f sp v rs m vtarg pd wt def) e (State f sp' w rs' m' wtarg pd' wt' def') ->
  v → w in f.(g).
Proof.
  intros. dependent destruction H.
  all: try enow eapply uniquesucc_edge_full in U; eauto.
  all: apply f.(DETOUR_SPEC), successors_spec; [now apply vertex_same; destruct pd | rewrite S; case b; [|apply in_cons]; apply in_eq].
Qed.

Lemma step_is_detour_1:
  forall ge f v w sp sp' rs rs' m m' wtarg pd pd' e wt wt' def def',
  step ge (State f sp v rs m v pd wt def) e (State f sp' w rs' m' wtarg pd' wt' def') ->
  v → wtarg in f.(g_pred) /\ w = detour f v wtarg.
Proof.
  intros. dependent destruction H. lia. lia.
  all: try (copy U; unfold uniquesucc in U0; case successors in U0; try congruence; case l in U0; try congruence; injection U0; intros).
  all: try (eapply uniquesucc_edge_full in U; eauto; subst; easy).
  split; auto.
  apply successors_spec. apply vertex_same; now destruct PD. rewrite S. case b; [|apply in_cons]; apply in_eq.
Qed.

Lemma step_is_detour_2:
  forall ge f v w sp sp' rs rs' m m' vtarg pd pd' e wt wt' def def',
  step ge (State f sp v rs m vtarg pd wt def) e (State f sp' w rs' m' vtarg pd' wt' def') ->
  v <> vtarg ->
  exists x, v → x in f.(g_pred) /\ w = detour f v x.
Proof.
  intros. dependent destruction H.
  all: try (copy U; unfold uniquesucc in U; case successors in U; try congruence; case l in U; try congruence; injection U; intros).
  all: try (eapply uniquesucc_edge_full in U0; eauto; decompose [and] U0; subst).
  * now exists w'.
  * exists (if b then ifso else ifnot). split; auto.
    apply successors_spec. apply vertex_same; now destruct PD. rewrite S. case b; [|apply in_cons]; apply in_eq.
  * lia.
Qed.