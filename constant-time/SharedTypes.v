Require Import Common Coqlib Classical Datatypes.
Require Import AST Memory Registers Maps Values Events Globalenvs Smallstep Integers Floats.
Require Import Smallstep Errors.
Require Import ListsExtra Before Permutation.
Require Import RTLtyping Op SafeOp.
Require Import Coq.Arith.Compare_dec.

(*** Instructions used in our intermediate languages ***)

Inductive instruction: Type :=
  | Inop: instruction
  | Iop: operation -> list reg -> reg -> instruction
  | Iload: memory_chunk -> addressing -> list reg -> reg -> instruction
  | Icond: condition -> list reg -> instruction
  | Ireturn: option reg -> instruction
  | Isel: typ -> reg (* cond *) -> reg (* x1 *) -> reg (* x2 *) -> reg (* dst *) -> instruction. (* only used after translating the predicated statements *)

Definition num_successors i := match i with
  | Inop | Iop _ _ _ | Iload _ _ _ _ | Isel _ _ _ _ _ => 1
  | Icond _ _ => 2
  | Ireturn _ => 0
end.

Definition instr_safe (i: instruction): Prop := match i with
  | Inop => True
  | Iop op args res => op_safe op
  | Iload chunk addr args dest => True (* we define Iload as safe here, but only allow its use at uniform pcs. *)
  | Icond cond args => condition_safe cond
  | Ireturn val => True
  | Isel _ _ _ _ _ => False (* not used during RTL -> GraphRTL translation *)
end.

(* After PCFL, conditions can also have only one successor *)
Definition min_successors (i: instruction) := match i with
  | Ireturn _ => 0 | _ => 1 end.

Definition instr_uses (i: instruction) : list reg :=
  match i with
  | Inop => nil
  | Iop op args res => args
  | Iload chunk addr args dest => args
  | Icond cond args => args
  | Ireturn None => nil
  | Ireturn (Some arg) => arg :: nil
  | Isel ty sel v1 v2 dst => sel :: v1 :: v2 :: nil
  end.

Definition instr_defs (i: instruction) : option reg :=
  match i with
  | Inop => None
  | Iop op args res => Some res
  | Iload chunk addr args dst => Some dst
  | Icond cond args => None
  | Ireturn optarg => None
  | Isel ty sel v1 v2 dst => Some dst
  end.

Definition node := positive.

Definition max_reg_instr (m: positive) (pc: node) (i: instruction) :=
  match i with
  | Inop => m
  | Iop op args res => fold_left Pos.max args (Pos.max res m)
  | Iload chunk addr args dest => fold_left Pos.max args (Pos.max dest m)
  | Icond cond args => fold_left Pos.max args m
  | Ireturn None => m
  | Ireturn (Some arg) => Pos.max arg m
  | Isel ty sel v1 v2 dst => fold_left Pos.max (sel :: v1 :: v2 :: nil) (Pos.max dst m)
  end.

Remark max_reg_instr_def:
  forall m i r pc, instr_defs i = Some r -> Ple r (max_reg_instr m pc i).
Proof.
  intros.
  assert (X: forall l n, Ple r n -> Ple r (fold_left Pos.max l n)).
  { induction l; simpl; intros. extlia. apply IHl. extlia. }
  destruct i; inv H.
- apply X. extlia.
- apply X. extlia.
- apply X. extlia.
Qed.

Remark max_reg_instr_uses:
  forall m pc i r, In r (instr_uses i) -> Ple r (max_reg_instr m pc i).
Proof.
  intros.
  assert (X: forall l n, In r l \/ Ple r n -> Ple r (fold_left Pos.max l n)).
  { induction l; simpl; intros.
    tauto.
    apply IHl. destruct H0 as [[A|A]|A]. right; subst; extlia. auto. right; extlia. }
  destruct i; simpl in *; try (apply X; auto).
- contradiction.
- destruct o; simpl in H; intuition. subst; extlia.
- simpl in *; decompose [or] H; auto; subst; extlia.
Qed.

Remark max_reg_instr_ge:
  forall m pc i, Ple m (max_reg_instr m pc i).
Proof.
  intros.
  assert (X: forall l n, Ple m n -> Ple m (fold_left Pos.max l n)).
  { induction l; simpl; intros.
    auto.
    apply IHl. extlia. }
  destruct i; simpl; try (destruct s0); repeat (apply X); try extlia.
  destruct o; extlia.
Qed.

Definition max_reg_function (code: PTree.t instruction) (params: list reg) :=
  Pos.max
    (PTree.fold max_reg_instr code 1%positive)
    (fold_left Pos.max params 1%positive).

Lemma max_reg_function_def:
  forall code params pc i r,
  code!pc = Some i -> instr_defs i = Some r -> Ple r (max_reg_function code params).
Proof.
  intros.
  assert (Ple r (PTree.fold max_reg_instr code 1%positive)).
  {  revert H.
     apply PTree_Properties.fold_rec with
       (P := fun c m => c!pc = Some i -> Ple r m).
   - intros. rewrite H in H1; auto.
   - rewrite PTree.gempty; congruence.
   - intros. rewrite PTree.gsspec in H3. destruct (peq pc k).
     + inv H3. eapply max_reg_instr_def; eauto.
     + apply Ple_trans with a. auto. apply max_reg_instr_ge.
  }
  unfold max_reg_function. extlia.
Qed.

Lemma max_reg_function_use:
  forall code params pc i r,
  code!pc = Some i -> In r (instr_uses i) -> Ple r (max_reg_function code params).
Proof.
  intros.
  assert (Ple r (PTree.fold max_reg_instr code 1%positive)).
  {  revert H.
     apply PTree_Properties.fold_rec with
       (P := fun c m => c!pc = Some i -> Ple r m).
   - intros. rewrite H in H1; auto.
   - rewrite PTree.gempty; congruence.
   - intros. rewrite PTree.gsspec in H3. destruct (peq pc k).
     + inv H3. eapply max_reg_instr_uses; eauto.
     + apply Ple_trans with a. auto. apply max_reg_instr_ge.
  }
  unfold max_reg_function. extlia.
Qed.

Lemma fold_max_spec: forall l m,
  fold_left Pos.max l m = Pos.max m (fold_left Pos.max l 1%positive).
Proof.
  intros. generalize dependent m. induction l. simpl. extlia.
  simpl. intro. replace (Pos.max 1 a) with a by extlia. case (plt m a); intro.
  * replace (Pos.max m a) with a by extlia. rewrite (IHl a). extlia.
  * replace (Pos.max m a) with m by extlia. rewrite (IHl m), (IHl a). extlia.
Qed.

Lemma fold_max_one: forall l,
  l = nil \/ In (fold_left Pos.max l 1%positive) l.
Proof.
  intros. induction l. now left. right.
  case IHl in *. subst. simpl. extlia.
  simpl. rewrite fold_max_spec. replace (Pos.max 1 a) with a by extlia.
  remember (fold_left _ _ _). case (plt a y); intro.
  * replace (Pos.max a y) with y by extlia; auto.
  * replace (Pos.max a y) with a by extlia; auto.
Qed.

Lemma fold_max_In: forall l m,
  m = fold_left Pos.max l m \/ (In (fold_left Pos.max l m) l).
Proof.
  intros. induction l. now left.
  simpl. case (plt a m) eqn:?.
  * replace (Pos.max m a) with m in * by extlia. case IHl; auto.
  * replace (Pos.max m a) with a in * by extlia.
  pose proof (fold_max_one l). rewrite fold_max_spec in *. remember (fold_left _ _ _).
  case IHl. extlia. intro. case (plt a y) eqn:?.
  + right. right. now repeat replace (Pos.max _ y) with y in * by extlia.
  + right. left. extlia.
Qed.

Lemma instr_uses_helper:
  forall pc i,
   (max_reg_instr 1 pc i) = 1%positive \/ In (max_reg_instr 1 pc i) (instr_uses i) \/ instr_defs i = Some (max_reg_instr 1 pc i).
Proof.
  intros.
  case i; simpl.
  * auto.
  * intros. right. replace (Pos.max r 1) with r by extlia. remember (fold_left Pos.max l r).
    case (peq p r); intro. right; now apply f_equal. left. rewrite Heqp. destruct (fold_max_In l r); congruence.
  * intros. right. replace (Pos.max r 1) with r by extlia. remember (fold_left Pos.max l r).
    case (peq p r); intro. right; now apply f_equal. left. rewrite Heqp. destruct (fold_max_In l r); congruence.
  * intros. destruct (fold_max_In l 1); auto.
  * intros. case o. intro. replace (Pos.max r 1) with r by extlia. right; left; apply in_eq. auto.
  * intros. simpl.
    replace (Pos.max r2 1) with r2 by extlia.
      case (plt r2 r) eqn:?; [replace (Pos.max r2 r) with r by extlia | replace (Pos.max r2 r) with r2 by extlia];
      try extlia.
    case (plt r2 r0) eqn:?; [replace (Pos.max r2 r0) with r0 by extlia | replace (Pos.max r2 r0) with r2 by extlia]; try extlia.
    case (plt r2 r1) eqn:?; [replace (Pos.max r2 r1) with r1 by extlia | replace (Pos.max r2 r1) with r2 by extlia]; try extlia.
    auto.
Qed.

Lemma max_reg_instr_function:
  forall code params pc i,
  code!pc = Some i -> Ple (max_reg_instr 1 pc i) (max_reg_function code params).
Proof.
  intros. decompose [or] (instr_uses_helper pc i).
  * extlia.
  * enow eapply max_reg_function_use.
  * enow eapply max_reg_function_def.
Qed.

Lemma max_reg_function_params:
  forall code params r, In r params -> Ple r (max_reg_function code params).
Proof.
  intros.
  assert (X: forall l n, In r l \/ Ple r n -> Ple r (fold_left Pos.max l n)).
  { induction l; simpl; intros.
    tauto.
    apply IHl. destruct H0 as [[A|A]|A]. right; subst; extlia. auto. right; extlia. }
  assert (Y: Ple r (fold_left Pos.max params 1%positive)).
  { apply X; auto. }
  unfold max_reg_function. extlia.
Qed.

(*** Welltypedness ***)

Section WellTyped.

Definition regenv := reg -> typ.

Inductive wt_instr (env: regenv) (sig: signature): instruction -> Prop :=
  | wt_Inop:
      wt_instr env sig Inop
  | wt_Iopmove:
      forall r1 r,
      env r = env r1 ->
      wt_instr env sig (Iop Omove (r1 :: nil) r)
  | wt_Iop:
      forall op args res,
      op <> Omove ->
      map env args = fst (type_of_operation op) ->
      env res = snd (type_of_operation op) ->
      wt_instr env sig (Iop op args res)
  | wt_Iload:
      forall chunk addr args dst,
      map env args = type_of_addressing addr ->
      env dst = type_of_chunk chunk ->
      wt_instr env sig (Iload chunk addr args dst)
  | wt_Isel:
      forall c ty r1 r2 dst,
      env c = Tint -> env r1 = ty -> env r2 = ty -> env dst = ty ->
      wt_instr env sig (Isel ty c r1 r2 dst)
  | wt_Icond:
      forall cond args,
      map env args = type_of_condition cond ->
      wt_instr env sig (Icond cond args)
  | wt_Ireturn_none:
      sig.(sig_res) = Tvoid ->
      wt_instr env sig (Ireturn None)
  | wt_Ireturn_some:
      forall arg ty,
      sig.(sig_res) <> Tvoid ->
      env arg = proj_sig_res sig ->
      env arg = ty ->
      wt_instr env sig (Ireturn (Some arg)).

Record wt_function (env: regenv) (code: PTree.t instruction) (params: list reg) (sig: signature): Prop :=
  mk_wt_function {
    wt_params:
      map env params = sig.(sig_args);
    wt_norepet:
      list_norepet params;
    wt_instrs:
      forall pc instr,
      code@!pc = Some instr -> wt_instr env sig instr;
  }.

Definition regset : Type := Regmap.t val.

Definition wt_regset (env: regenv) (rs: regset) : Prop :=
  forall r, Val.has_type (rs#r) (env r).


Lemma wt_regset_assign:
  forall env rs v r,
  wt_regset env rs ->
  Val.has_type v (env r) ->
  wt_regset env (rs#r <- v).
Proof.
  intros; red; intros.
  rewrite Regmap.gsspec.
  case (peq r0 r); intro.
  subst r0. assumption.
  apply H.
Qed.

Lemma wt_regset_list:
  forall env rs,
  wt_regset env rs ->
  forall rl, Val.has_type_list (rs##rl) (List.map env rl).
Proof.
  induction rl; simpl.
  auto.
  split. apply H. apply IHrl.
Qed.

Lemma wt_regset_setres:
  forall env rs v res,
  wt_regset env rs ->
  Val.has_type v (type_of_builtin_res env res) ->
  wt_regset env (regmap_setres res v rs).
Proof.
  intros. destruct res; simpl in *; auto. apply wt_regset_assign; auto.
Qed.

Lemma lessdef_wt: forall rs rs' env,
  regs_lessdef rs rs' ->
  wt_regset env rs' -> wt_regset env rs.
Proof.
  intros. intro.
  enough (X: forall a b ty, Val.lessdef a b -> Val.has_type b ty -> Val.has_type a ty). pose (H r). pose (H0 r). enow eapply X.
  intros. now case a, b, ty.
Qed.

Lemma wt_lessdef_set:
  forall rs rs' env r v,
  regs_lessdef rs rs' ->
  wt_regset env rs' ->
  wt_regset env (rs # r <- v) ->
  wt_regset env (rs' # r <- v).
Proof.
  intros. intro. pose proof (H1 r0). case (peq r r0) eqn:?.
  * rewrite e in *. now rewrite Regmap.gss in *.
  * rewrite Regmap.gso in *; auto.
Qed.

Lemma wt_exec_Iop:
  forall fd (ge: Genv.t fd unit) env sig sp op args res rs m v,
  wt_instr env sig (Iop op args res) ->
  eval_operation ge sp op rs##args m = Some v ->
  wt_regset env rs ->
  wt_regset env (rs#res <- v).
Proof.
  intros. inv H.
  simpl in H0. inv H0. apply wt_regset_assign; auto.
  rewrite H3; auto.
  eapply wt_regset_assign; auto.
  rewrite H7. eapply type_of_operation_sound; eauto.
Qed.

Lemma wt_exec_Iload:
  forall env sig chunk addr args dst m a v rs,
  wt_instr env sig (Iload chunk addr args dst) ->
  Mem.loadv chunk m a = Some v ->
  wt_regset env rs ->
  wt_regset env (rs#dst <- v).
Proof.
  intros. destruct a; simpl in H0; try discriminate. inv H.
  eapply wt_regset_assign; eauto. rewrite H7; eapply Mem.load_type; eauto.
Qed.

Lemma wt_instr_at:
  forall code env params sig pc i,
  wt_function env code params sig -> code@!pc = Some i -> wt_instr env sig i.
Proof.
  intros. inv H. eauto.
Qed.

(* No Tany32, Tany64 types - these are not produced by RTLTyping but are in the way of one proof of
   zeroed-out registers *)

Definition is_normal_ty (ty: typ) := match ty with
  | Tany32 | Tany64 => False
  | _ => True
end.

Definition is_normal_ty_dec: forall ty, {is_normal_ty ty} + {~ is_normal_ty ty}.
Proof.
  unfold is_normal_ty.
  intro. enow case ty.
Qed.

Definition any_free_regenv (env: regenv) (max: Pos.t) := forall r, Ple r max -> is_normal_ty (env r).

Definition decide_any_free_regenv (env: regenv) (max: Pos.t) :=
  forallb (fun r => (is_normal_ty_dec (env (Pos.of_succ_nat r)))) (seq 0 (Pos.to_nat max)).

Lemma any_free_regenv_dec: forall env max,
  {any_free_regenv env max} + {~ any_free_regenv env max}.
Proof.
  intros.
  case (decide_any_free_regenv env max) eqn:?; unfold any_free_regenv, decide_any_free_regenv in *.
  * left. intros.
    rewrite forallb_forall in Heqb. pose proof (Heqb (Pos_to_pred_nat r)).
    exploit H0. apply in_seq. unfold Pos_to_pred_nat. extlia.
    intro. case is_normal_ty_dec in H1. clear H1. now rewrite succpred in i. inv H1.
  * right. intro. eassert (~ forallb _ _ = true) by now rewrite Heqb.
    rewrite forallb_forall in H0. apply H0. intros. exploit H. Unshelve. 3: exact (Pos.of_succ_nat x).
    apply in_seq in H1. extlia. now case is_normal_ty_dec.
Qed.

End WellTyped.


(*** Definedness ***)

Section Definedness.

Definition def_regset (max: reg) (regs: regset) := forall r, Ple r max <-> regs#r <> Vundef.

Lemma def_regset_assign:
  forall max rs v r,
  def_regset max rs ->
  v <> Vundef ->
  Ple r max ->
  def_regset max (rs#r <- v).
Proof.
   intros; red; intros.
   rewrite Regmap.gsspec.
   case (peq r0 r); split; intro.
   * auto.
   * extlia.
   * now apply H.
   * now apply H.
Qed.

Definition def_args (args: list val) := forall r, In r args -> r <> Vundef.

Lemma def_args_get:
  forall rs regs max,
  def_regset max rs ->
  (forall r, In r regs -> Ple r max) ->
  def_args (rs##regs).
Proof.
  intros. induction regs.
  * easy.
  * intro. intro. case H1; intro.
  + rewrite <- H2. apply H, H0, in_eq.
  + apply IHregs; auto. intros. apply H0, in_cons, H3.
Qed.


(*** Initialization ***)

Definition default_value (t: typ) := match t with
  | Tint => Vint (Int.zero)
  | Tfloat => Vfloat (Float.zero)
  | Tlong => Vlong (Int64.zero)
  | Tsingle => Vsingle (Float32.zero)
  | Tany32 => Vint (Int.zero)
  | Tany64 => Vlong (Int64.zero)
end.

Lemma default_value_type: forall t,
  Val.has_type (default_value t) t.
Proof.
  intros. case t; easy.
Qed.

Lemma default_value_def: forall t,
  default_value t <> Vundef.
Proof.
  intros. case t; easy.
Qed.

Local Transparent Val.eq.

Fixpoint init_all_regs' (env: regenv) (args: list val) (params: list reg) (max: nat) := match max with
  | 0 => RTL.init_regs args params
  | S p =>
    let r := Pos.of_succ_nat p in
    let rs := init_all_regs' env args params p in
    if Val.eq Vundef (rs # r) then Regmap.set r (default_value (env r)) rs else rs
end.

Lemma rtl_init_regs_undef_spec: forall params args reg max,
  (forall p, In p params -> Ple p max) ->
  Plt max reg ->
  (RTL.init_regs args params) # reg = Vundef.
Proof.
  intros. generalize dependent args. induction params. simpl. auto.
  intros. simpl. case args. auto. intros. case (peq a reg); intro.
  * assert (In a (a::params)) by apply in_eq. apply H in H1. extlia.
  * rewrite Regmap.gso, IHparams; auto. intros. apply H, in_cons, H1.
Qed.

Lemma init_all_regs'_undef_spec: forall params env args reg max,
  Vundef = ((init_all_regs' env args params max) # reg) ->
  Vundef = ((RTL.init_regs args params) # reg).
Proof.
  intros. induction max. now simpl in H.
  case (peq reg (Pos.of_succ_nat max)) eqn:?.
  * simpl in H. rewrite <- e in *. case ((init_all_regs' env args params max) !! reg) in H; simpl in H; auto.
    + rewrite Regmap.gss in H. case (env reg) in H; simpl in H; congruence.
  * simpl in H. case ((init_all_regs' env args params max) !! (Pos.of_succ_nat max)) in H; simpl in H; auto.
    + rewrite Regmap.gso in H; auto.
Qed.

Lemma init_all_regs'_def_spec: forall params env args reg max,
  ((RTL.init_regs args params) # reg) <> Vundef ->
  ((init_all_regs' env args params max) # reg) = ((RTL.init_regs args params) # reg).
Proof.
  intros. induction max. now simpl in H.
  case (peq reg (Pos.of_succ_nat max)) eqn:?.
  * simpl. rewrite <- e in *. case ((init_all_regs' env args params max) !! reg) eqn:?; simpl; congruence.
  * simpl. case ((init_all_regs' env args params max) !! (Pos.of_succ_nat max)) eqn:?.
    simpl. now rewrite Regmap.gso.
    all: easy.
Qed.

Lemma init_all_regs'_undef_spec_2: forall params env args reg max,
  ~ Plt reg (Pos.of_succ_nat max) ->
  (init_all_regs' env args params max) # reg = (RTL.init_regs args params) # reg.
Proof.
  intros. induction max. auto.
  case (peq reg (Pos.of_succ_nat max)) eqn:?. extlia.
  simpl. case _ !! (Pos.of_succ_nat max) eqn:?; try rewrite Regmap.gso; try apply IHmax; extlia. 
Qed.

Lemma init_all_regs_spec: forall params env args reg max,
  Plt reg (Pos.of_succ_nat max) ->
  (init_all_regs' env args params max) # reg =
    if Val.eq Vundef ((RTL.init_regs args params) # reg) then
      default_value (env reg)
    else
      (RTL.init_regs args params) # reg.
Proof.
  intros.
  case ((RTL.init_regs args params) # reg) eqn:?.
  2-6: simpl; rewrite init_all_regs'_def_spec; [auto|congruence].
  simpl. induction max. extlia.
  case (peq reg (Pos.of_succ_nat max)) eqn:?.
  * simpl. rewrite <- e in *. rewrite init_all_regs'_undef_spec_2; [|extlia].
    case ((RTL.init_regs args params) # reg) in *; try congruence.
    now apply Regmap.gss.
  * simpl. case _ !! (Pos.of_succ_nat max) eqn:?; try rewrite Regmap.gso; auto; apply IHmax; extlia.
Qed.

Lemma init_all_regs_step_unfold_1: forall params env args max,
  In (Pos.of_nat (S max)) params ->
  length params = length args ->
  (forall a, In a args -> a <> Vundef) ->
  init_all_regs' env args params (S max) = init_all_regs' env args params max.
Proof.
  intros. simpl.
  case ((init_all_regs' env args params max) !! (Pos.of_succ_nat max)) eqn:?; auto.
  symmetry in Heqv. apply init_all_regs'_undef_spec in Heqv.
  exfalso. generalize dependent params. induction args. now case params in *.
  case params in *; auto. intros.
  simpl in Heqv.
  case (peq p (Pos.of_succ_nat max)) eqn:?.
  * rewrite e, Regmap.gss in Heqv. symmetry in Heqv. now apply H1 in Heqv; [|apply in_eq].
  * rewrite Regmap.gso in Heqv; auto. apply IHargs in Heqv; auto. 
  + intros. apply H1, in_cons, H2.
  + case H eqn:?; auto; extlia.
Qed.

Lemma init_all_regs_step_unfold_2: forall params env args max,
  ~ In (Pos.of_nat (S max)) params ->
  init_all_regs' env args params (S max) = Regmap.set (Pos.of_succ_nat max) (default_value (env (Pos.of_succ_nat max))) (init_all_regs' env args params max).
Proof.
  intros. simpl.
  enough ((RTL.init_regs args params) !! (Pos.of_succ_nat max) = Vundef).
  case ((init_all_regs' env args params max) !! (Pos.of_succ_nat max)) eqn:?; auto;
    (rewrite init_all_regs'_undef_spec_2 in Heqv; [congruence | extlia]).
  generalize dependent args. induction params; intro. auto.
  case args. auto. intros. simpl. case (peq a (Pos.of_succ_nat max)); intro.
  + exfalso. rewrite e in H. apply H. left. extlia.
  + rewrite Regmap.gso; [|extlia]. apply IHparams. intro. apply H, in_cons, H0.
Qed.


Definition init_all_regs (env: regenv) (code: PTree.t instruction) (params: list reg) (args: list val) := init_all_regs' env args params (Pos.to_nat (max_reg_function code params)).

Lemma init_all_regs'_wt: forall env params args reg,
  wt_regset env (init_all_regs' env args params reg) ->
  wt_regset env (init_all_regs' env args params (S reg)).
Proof.
  intros. simpl.
  case (_ !! _) eqn:?; auto.
  * apply wt_regset_assign. auto. apply default_value_type.
Qed.

Lemma init_all_regs_wt: forall env sig params code args,
  Val.has_type_list args sig.(sig_args) ->
  map env params = sig_args sig ->
  wt_regset env (init_all_regs env code params args).
Proof.
  intros.
  assert (wt_regset env (RTL.init_regs args params)) by (apply RTLtyping.wt_init_regs; now rewrite H0).
  unfold wt_regset in *. intros.
  case (le_dec (Pos_to_pred_nat r) (Pos_to_pred_nat (max_reg_function code params))); intro.
  * unfold init_all_regs. rewrite init_all_regs_spec by (unfold Pos_to_pred_nat in l; extlia).
    case _ !! r eqn:?; simpl; [apply default_value_type | | | | |]; simpl; specialize H1 with r; now rewrite Heqy in H1.
  * unfold init_all_regs. rewrite init_all_regs'_undef_spec_2 by (unfold Pos_to_pred_nat in n; extlia).
    apply H1.
Qed.

Lemma init_all_regs_def: forall env params code args,
  def_regset (max_reg_function code params) (init_all_regs env code params args).
Proof.
  intros.
  unfold def_regset. intros. unfold init_all_regs. split; intro.
  * rewrite init_all_regs_spec by extlia.
    case _ !! r eqn:?; simpl; [apply default_value_def | | | | |]; congruence.
  * case (plt r (max_reg_function code params)); intro. extlia. case (peq r (max_reg_function code params)); intro. extlia.
    exfalso. apply H. rewrite init_all_regs'_undef_spec_2. 2: extlia.
    eapply rtl_init_regs_undef_spec. eapply max_reg_function_params. Unshelve. 2: exact code. extlia.
Qed.

Lemma init_all_rtl_lessdef: forall env params code args,
  regs_lessdef (RTL.init_regs args params) (init_all_regs env code params args).
Proof.
  intros.
  unfold regs_lessdef. intro r.
  case (le_dec (Pos_to_pred_nat r) (Pos_to_pred_nat (max_reg_function code params))); intro.
  * unfold init_all_regs. rewrite init_all_regs_spec by (unfold Pos_to_pred_nat in l; extlia).
    case ((RTL.init_regs args params) # r); easy.
  * unfold init_all_regs. rewrite init_all_regs'_undef_spec_2 by (unfold Pos_to_pred_nat in n; extlia).
    easy.
Qed.

Lemma init_all_regs'_env_inv: forall env1 env2 args params max,
  (forall m, m < max -> env1 (Pos.of_succ_nat m) = env2 (Pos.of_succ_nat m)) ->
  init_all_regs' env1 args params max = init_all_regs' env2 args params max.
Proof.
  intros. induction max. auto.
  assert (IH: forall m : nat, m < max -> env1 (Pos.of_succ_nat m) = env2 (Pos.of_succ_nat m)) by (intros; apply H; lia).
  pose proof (IHmax IH). simpl.
  case (_ !! _) eqn:? in |- *; case (_ !! _) eqn:? in |- *.
  now rewrite H0, H; [|lia].
  all: rewrite H0, Heqy0 in Heqy; congruence.
Qed.

Lemma env_inv_conv: forall (env1 env2: regenv) max,
  (forall m, Ple m max -> env1 m = env2 m) ->
  (forall m, m < (Pos.to_nat max) -> env1 (Pos.of_succ_nat m) = env2 (Pos.of_succ_nat m)).
Proof.
  intros. rewrite H. auto. extlia.
Qed.

Lemma wt_regset_env_inv: forall rs env1 env2 max,
  def_regset max rs ->
  (forall m, Ple m max -> env1 m = env2 m) ->
  wt_regset env1 rs ->
  wt_regset env2 rs.
Proof.
  unfold wt_regset. intros.
  case (plt max r) eqn:?.
  * assert (~Ple r max) by extlia. unfold def_regset in H. rewrite H in H2. replace (rs !! r) with Vundef.
    easy. case (rs !! r) eqn:?; try congruence; exfalso; apply H2; easy.
  * rewrite <- H0. apply H1. extlia.
Qed.


(* Handling complex reg_lessdefs *)

Lemma regs_lessdef_refl: forall rs,
  regs_lessdef rs rs.
Proof.
  easy.
Qed.

Lemma val_lessdef_trans: forall v1 v2 v3,
  Val.lessdef v1 v2 -> Val.lessdef v2 v3 -> Val.lessdef v1 v3.
Proof.
  intros. now inv H; inv H0.
Qed.

Lemma regs_lessdef_trans: forall r1 r2 r3,
  regs_lessdef r1 r2 -> regs_lessdef r2 r3 -> regs_lessdef r1 r3.
Proof.
  unfold regs_lessdef. intros. enow eapply val_lessdef_trans.
Qed.

Lemma lessdef_new_six: forall rs' rs r1 v1 r2 v2 r3 v3 r4 v4 r5 v5 r6 v6,
  regs_lessdef rs' rs ->
  rs' # r1 = Vundef -> rs' # r2 = Vundef -> rs' # r3 = Vundef -> rs' # r4 = Vundef -> rs' # r5 = Vundef -> rs' # r6 = Vundef ->
  regs_lessdef rs' rs # r1 <- v1 # r2 <- v2 # r3 <- v3 # r4 <- v4 # r5 <- v5 # r6 <- v6.
Proof.
  intros. intro. case (peq r r6) eqn:?.
  * rewrite e, Regmap.gss, H5. apply Val.lessdef_undef.
  * case (peq r r5) eqn:?.
  + rewrite e, Regmap.gso, Regmap.gss, H4; try lia. apply Val.lessdef_undef. 
  + case (peq r r4) eqn:?.
  - rewrite e, Regmap.gso, Regmap.gso, Regmap.gss, H3; try lia. apply Val.lessdef_undef.
  - case (peq r r3) eqn:?.
  ** rewrite e, Regmap.gso, Regmap.gso, Regmap.gso, Regmap.gss, H2; try lia. apply Val.lessdef_undef.
  ** case (peq r r2) eqn:?.
  ++ rewrite e, Regmap.gso, Regmap.gso, Regmap.gso, Regmap.gso, Regmap.gss, H1; try lia. apply Val.lessdef_undef.
  ++ case (peq r r1) eqn:?.
  -- rewrite e, Regmap.gso, Regmap.gso, Regmap.gso, Regmap.gso, Regmap.gso, Regmap.gss, H0; try lia. apply Val.lessdef_undef.
  -- rewrite Regmap.gso, Regmap.gso, Regmap.gso, Regmap.gso, Regmap.gso, Regmap.gso; try lia. apply H.
Qed.

Lemma lessdef_new_five: forall rs' rs r1 v1 r2 v2 r3 v3 r4 v4 r5 v5,
  regs_lessdef rs' rs ->
  rs' # r1 = Vundef -> rs' # r2 = Vundef -> rs' # r3 = Vundef -> rs' # r4 = Vundef -> rs' # r5 = Vundef ->
  regs_lessdef rs' rs # r1 <- v1 # r2 <- v2 # r3 <- v3 # r4 <- v4 # r5 <- v5.
Proof.
  intros. replace (rs # r1 <- v1) with (rs # r1 <- v1 # r1 <- v1) by apply Regmap.set2.
  now apply lessdef_new_six; auto.
Qed.

Lemma lessdef_new_four: forall rs' rs r1 v1 r2 v2 r3 v3 r4 v4,
  regs_lessdef rs' rs ->
  rs' # r1 = Vundef -> rs' # r2 = Vundef -> rs' # r3 = Vundef -> rs' # r4 = Vundef ->
  regs_lessdef rs' rs # r1 <- v1 # r2 <- v2 # r3 <- v3 # r4 <- v4.
Proof.
  intros. replace (rs # r1 <- v1) with (rs # r1 <- v1 # r1 <- v1) by apply Regmap.set2.
  now apply lessdef_new_five; auto.
Qed.

Lemma lessdef_new_three: forall rs' rs r1 v1 r2 v2 r3 v3,
  regs_lessdef rs' rs ->
  rs' # r1 = Vundef -> rs' # r2 = Vundef -> rs' # r3 = Vundef ->
  regs_lessdef rs' rs # r1 <- v1 # r2 <- v2 # r3 <- v3.
Proof.
  intros. replace (rs # r1 <- v1) with (rs # r1 <- v1 # r1 <- v1) by apply Regmap.set2.
  now apply lessdef_new_four; auto.
Qed.

Lemma lessdef_new_two: forall rs' rs r1 v1 r2 v2,
  regs_lessdef rs' rs ->
  rs' # r1 = Vundef -> rs' # r2 = Vundef ->
  regs_lessdef rs' rs # r1 <- v1 # r2 <- v2.
Proof.
  intros. replace (rs # r1 <- v1) with (rs # r1 <- v1 # r1 <- v1) by apply Regmap.set2.
  now apply lessdef_new_three; auto.
Qed.

Lemma lessdef_new_one: forall rs' rs r1 v1,
  regs_lessdef rs' rs ->
  rs' # r1 = Vundef ->
  regs_lessdef rs' rs # r1 <- v1.
Proof.
  intros. replace (rs # r1 <- v1) with (rs # r1 <- v1 # r1 <- v1) by apply Regmap.set2.
  now apply lessdef_new_two; auto.
Qed.


Lemma regs_def_same: forall rs1 rs2 args max,
  regs_lessdef rs1 rs2 ->
  def_regset max rs1 ->
  (forall a, In a args -> Ple a max) ->
  rs1 ## args = rs2 ## args.
Proof.
  intros. induction args. auto.
  simpl. rewrite IHargs by (intros; now apply H1, in_cons). f_equal.
  pose proof H a.
  assert (Ple a max) by apply H1, in_eq. apply H0 in H3.
  inv H2; congruence.
Qed.

Lemma map_set_swap: forall (rs: regset) r1 v1 r2 v2,
  r1 <> r2 ->
  rs # r1 <- v1 # r2 <- v2 = 
  rs # r2 <- v2 # r1 <- v1.
Proof.
  intros. destruct rs. apply pair_equal_spec. split; auto.
  simpl. apply PTree.extensionality. intro.
  case (peq i r1); intro.
    rewrite e. now rewrite PTree.gso, PTree.gss, PTree.gss.
  case (peq i r2); intro.
    rewrite e. rewrite PTree.gss, PTree.gso, PTree.gss. auto. lia.
  repeat rewrite PTree.gso; auto; lia. 
Qed.

Lemma map_set_move_front_4: forall (rs: regset) r1 v1 r2 v2 r3 v3 r4 v4,
  r1 <> r4 -> r2 <> r4 -> r3 <> r4 ->
  rs # r1 <- v1 # r2 <- v2 # r3 <- v3 # r4 <- v4 = 
  rs # r4 <- v4 # r1 <- v1 # r2 <- v2 # r3 <- v3.
Proof.
  intros. now repeat rewrite map_set_swap with (r2:=r4).
Qed.

Lemma map_set_move_front_5: forall (rs: regset) r1 v1 r2 v2 r3 v3 r4 v4 r5 v5,
  r1 <> r5 -> r2 <> r5 -> r3 <> r5 -> r4 <> r5 ->
  rs # r1 <- v1 # r2 <- v2 # r3 <- v3 # r4 <- v4 # r5 <- v5 = 
  rs # r5 <- v5 # r1 <- v1 # r2 <- v2 # r3 <- v3 # r4 <- v4.
Proof.
  intros. now repeat rewrite map_set_swap with (r2:=r5).
Qed.

Lemma lessdef_set_same: forall rs r,
  regs_lessdef rs (rs # r <- (rs # r)).
Proof.
  intros. intro. case (peq r r0); intro.
  * rewrite e, Regmap.gss. now apply Val.lessdef_same.
  * rewrite Regmap.gso. now apply Val.lessdef_same. lia.
Qed.

(* Specific applications required in the pred->sel simulation proofs *)

Lemma lessdef_new_special_six_four_nop: forall rs' rs r1 v1 r2 v2 r3 v3 r4 r5 v5 r6 v6,
  regs_lessdef rs' rs ->
  r1 <> r4 -> r2 <> r4 -> r3 <> r4 -> r4 <> r5 -> r4 <> r6 ->
  rs' # r1 = Vundef -> rs' # r2 = Vundef -> rs' # r3 = Vundef -> rs' # r5 = Vundef -> rs' # r6 = Vundef ->
  regs_lessdef rs' rs # r1 <- v1 # r2 <- v2 # r3 <- v3 # r4 <- ((rs # r1 <- v1 # r2 <- v2 # r3 <- v3) # r4) # r5 <- v5 # r6 <- v6.
Proof.
  intros.
  rewrite map_set_move_front_4 with (r4:=r4); auto.
  eenough (E: _ !! r4 = rs !! r4). rewrite E.
  eapply regs_lessdef_trans; [apply lessdef_set_same with (r:=r4) | apply lessdef_new_five].
  now apply set_reg_lessdef.
  all: repeat rewrite Regmap.gso; auto; lia.
Qed.

Lemma lessdef_new_special_six_four_op: forall rs' rs r1 v1 r2 v2 r3 v3 r4 r5 v5 r6 v6,
  regs_lessdef rs' rs ->
  r1 <> r4 -> r2 <> r4 -> r3 <> r4 -> r4 <> r5 -> r4 <> r6 ->
  rs' # r1 = Vundef -> rs' # r2 = Vundef -> rs' # r3 = Vundef -> rs' # r5 = Vundef -> rs' # r6 = Vundef ->
  regs_lessdef (rs' # r4 <- v3) (rs # r1 <- v1 # r2 <- v2 # r3 <- v3 # r4 <- ((rs # r1 <- v1 # r2 <- v2 # r3 <- v3) # r3) # r5 <- v5 # r6 <- v6).
Proof.
  intros.
  rewrite map_set_move_front_4 with (r4:=r4); auto.
  eenough (E: _ !! r3 = v3). rewrite E.
  eapply regs_lessdef_trans; [apply lessdef_set_same with (r:=r4) | apply lessdef_new_five].
  rewrite Regmap.gss, Regmap.set2. now apply set_reg_lessdef.
  all: try (rewrite Regmap.gss, Regmap.gso, Regmap.gso; auto; lia).
  now rewrite Regmap.gss.
Qed.

Lemma lessdef_new_special_five_four_op: forall rs' rs r1 v1 r2 v2 r3 v3 r4 v4 r5,
  regs_lessdef rs' rs ->
  r1 <> r5 -> r1 <> r4 -> r2 <> r5 -> r2 <> r4 -> r3 <> r5 -> r3 <> r4 -> r4 <> r5 ->
  rs' # r1 = Vundef -> rs' # r2 = Vundef -> rs' # r4 = Vundef -> rs' # r5 = Vundef ->
  regs_lessdef (rs' # r3 <- v3) (rs # r1 <- v1 # r2 <- v2 # r3 <- v3 # r4 <- v4 # r5 <- ((rs # r1 <- v1 # r2 <- v2 # r3 <- v3 # r4 <- v4) # r4)).
Proof.
  intros.
  rewrite map_set_move_front_5 with (r5:=r5); auto.
  rewrite map_set_move_front_5 with (r5:=r4); auto.
  apply set_reg_lessdef. apply Val.lessdef_refl.
  now apply lessdef_new_four.
Qed.

Lemma same_regvalues: forall (rs1 rs2: regset) max args,
  (forall i, Ple i max -> rs1 # i = rs2 # i) -> 
  (forall a, In a args -> Ple a max) ->
  rs1 ## args = rs2 ## args.
Proof.
  intros. induction args. auto.
  simpl. rewrite IHargs by (intros; now apply H0, in_cons).
  f_equal. apply H, H0, in_eq.
Qed.

End Definedness.