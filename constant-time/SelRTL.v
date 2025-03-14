Require Import Common Coqlib Classical Datatypes.
Require Import AST RTL Memory Registers Maps Values Events Globalenvs Smallstep Op Integers.
Require Import Graph GraphDual.
Require Import Smallstep Errors.
Require Import ListsExtra Before Permutation.
Require Import SharedTypes.
Require Import Coq.Program.Equality.

Record function : Type := mkfunction {
  code: PTree.t instruction;
  sig: signature;
  params: list reg;
  stacksize: Z;
  taint_attr: fun_taint_attr reg;
  g: G;
  entry: nat;
  exit: nat;
  n: nat;

  N: n > 0;
  VS: g.(vs) = seq 0 n;
  NCODE: forall pc, code @! pc <> None <-> pc < n;
  SUCCS: forall pc i, code @! pc = Some i -> length (successors g pc) = num_successors i;
  ENTRY: vertex g entry;
  EXIT: forall v, v = exit <-> is_exit g v;

  env: regenv;
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

(*** SELECTION DEFINITION ***)

Definition eval_sel (sel: reg) (r1 r2: reg) (rs: regset) (ty: typ): val :=
  Val.select (Coqlib.option_map negb (Val.maskzero_bool (rs#sel) Int.one)) (rs#r1) (rs#r2) ty.

Lemma normalize_lessdef:
  forall rs rs' r ty,
  regs_lessdef rs rs' ->
  Val.lessdef (Val.normalize rs !! r ty) (Val.normalize rs' !! r ty).
Proof.
  intros. case (rs !! r) eqn:?, ty eqn:?; simpl; auto;
  case (rs' !! r) eqn:?; try (pose (H r); rewrite Heqv, Heqv0 in l; inv l);
  now simpl.
Qed.

Lemma eval_sel_lessdef:
  forall sel r r0 rs ty rs',
  regs_lessdef rs rs' ->
  Val.lessdef (eval_sel sel r r0 rs ty) (eval_sel sel r r0 rs' ty).
Proof.
  intros.
  unfold eval_sel. simpl.
  case (rs !! sel) eqn:?; simpl; auto.
  case (rs' !! sel) eqn:?; try (pose (H sel); rewrite Heqv, Heqv0 in l; inv l); simpl.
  case negb; now apply normalize_lessdef.
Qed.

(*** STATE + STEP ***)  


Inductive state : Type :=
  | State: forall (f: function)
                  (sp: val)
                  (pc: nat)
                  (rs: regset)
                  (m: mem)
                  (WT: wt_regset f.(env) rs),
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
      forall f sp pc rs m pc' wt,
      getinstr f pc = Some(Inop) ->
      uniquesucc f pc = Some pc' ->
      step (State f sp pc rs m wt)
        E0 (State f sp pc' rs m wt)
  | exec_Iop:
      forall f sp pc rs m op args res pc' v wt wt' 
      (I: getinstr f pc = Some(Iop op args res))
      (U: uniquesucc f pc = Some pc')
      (OP: eval_operation ge sp op rs##args m = Some v),
      step (State f sp pc rs m wt)
        E0 (State f sp pc' (rs#res <- v) m wt')
  | exec_Iload:
      forall f sp pc pc' rs m chunk addr args dst a val wt wt'
      (I: getinstr f pc = Some(Iload chunk addr args dst))
      (U: uniquesucc f pc = Some pc')
      (AD: eval_addressing ge sp addr rs##args = Some a)
      (MEM: Mem.loadv chunk m a = Some val),
      step (State f sp pc rs m wt)
        E0 (State f sp pc' (rs#dst <- val) m wt')
  | exec_Icond:
      forall f sp pc rs m cond args ifso ifnot b pc' wt,
      getinstr f pc = Some(Icond cond args) ->
      successors f.(g) pc = ifso::ifnot::nil ->
      eval_condition cond rs##args m = Some b ->
      pc' = (if b then ifso else ifnot) ->
      step (State f sp pc rs m wt)
        E0 (State f sp pc' rs m wt)
  | exec_Isel:
      forall f sp pc rs m ty sel r1 r2 res v pc' wt wt'
      (I: getinstr f pc = Some(Isel ty sel r1 r2 res))
      (U: uniquesucc f pc = Some pc')
      (S: eval_sel sel r1 r2 rs ty = v),
      step (State f sp pc rs m wt)
        E0 (State f sp pc' (rs#res <- v) m wt')
  | exec_function_internal:
      forall f args m m' stk wt wt' def,
      Mem.alloc m 0 f.(stacksize) = (m', stk) ->
      step (InitState (Internal f) args m wt def)
        E0 (State f
                  (Vptr stk Ptrofs.zero)
                  f.(entry)
                  (RTL.init_regs args f.(params))
                  m'
                  wt'
                  )
  | exec_function_external:
      forall f args res t m m' wt def,
      external_call f ge args m t res m' ->
      step (InitState (External f) args m wt def)
         t (EndState (External f) res m')
  | exec_Ireturn:
      forall f stk pc rs m or m' wt,  
      getinstr f pc = Some(Ireturn or) ->
      successors f.(g) pc = nil ->
      Mem.free m stk 0 f.(stacksize) = Some m' ->
      step (State f (Vptr stk Ptrofs.zero) pc rs m wt)
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

(* Any valid step corresponds to an edge in the graph *)
Theorem step_is_edge: forall ge t f sp sp' pc pc' rs rs' m m' wt wt'  ,
  step ge (State f sp pc rs m wt ) t (State f sp' pc' rs' m' wt' ) ->
  pc → pc' in f.(g).
Proof.
  intros. dependent destruction H.
  all: try enow eapply uniquesucc_edge.
  * apply getinstr_vertex in H. apply successors_spec with (w := if b then ifso else ifnot) in H. apply H. rewrite H0.
    case b; [|apply in_cons]; apply in_eq.
Qed.