Require Import Common Coqlib Classical Datatypes.
Require Import AST RTL Memory Registers Maps Values Events Globalenvs Smallstep Op Integers.
Require Import ListsExtra Graph GraphDual SharedTypes.
Require Import Smallstep Errors Linking.
Require Import Predication Sim1RTLToGraph Sim2GraphToPred Sim3PredToSel Sim4SelToRTL.

Parameter print_GraphRTL: Z -> GraphRTL.program -> unit.
Parameter print_PredRTL: Z -> PredRTL.program -> unit.

(* In this file, the four passes required for the constant-time transform are combined into a single pass. *)

Definition apply_total (A B: Type) (x: res A) (f: A -> B) : res B :=
  match x with Error msg => Error msg | OK x1 => OK (f x1) end.

Definition apply_partial (A B: Type)
                         (x: res A) (f: A -> res B) : res B :=
  match x with Error msg => Error msg | OK x1 => f x1 end.

Notation "a @@@ b" :=
   (apply_partial _ _ a b) (at level 50, left associativity).
Notation "a @@ b" :=
   (apply_total _ _ a b) (at level 50, left associativity).

Definition print {A: Type} (printer: A -> unit) (prog: A) : A :=
  let unused := printer prog in prog.

Definition time {A B: Type} (name: string) (f: A -> B) : A -> B := f.

Lemma print_identity:
  forall (A: Type) (printer: A -> unit) (prog: A),
  print printer prog = prog.
Proof.
  intros; unfold print. destruct (printer prog); auto.
Qed.

Lemma compose_print_identity:
  forall (A: Type) (x: res A) (f: A -> unit),
  x @@ print f = x.
Proof.
  intros. destruct x; simpl. rewrite print_identity. auto. auto.
Qed.


Section Transform.

Definition transf_program (f: program) : res program :=
   OK f
  @@@ time "CT1" Sim1RTLToGraph.transf_program
   @@ print (print_GraphRTL 1)
   @@ time "CT2" Sim2GraphToPred.transf_program
   @@ print (print_PredRTL 2)
  @@@ time "CT3" Predication.transf_program
  @@@ time "CT4" Sim4SelToRTL.transf_program.


Local Open Scope linking_scope.

Definition ct_passes :=
      mkpass Sim1RTLToGraph.match_prog
  ::: mkpass Sim2GraphToPred.match_prog
  ::: mkpass Sim3PredToSel.match_prog
  ::: mkpass Sim4SelToRTL.match_prog
  ::: pass_nil _.

Definition match_prog: program -> program -> Prop :=
  pass_match (compose_passes ct_passes).

Theorem transf_program_match:
  forall p tp,
  transf_program p = OK tp ->
  match_prog p tp.
Proof.
  intros p tp T.
  unfold transf_program, time in T. simpl in T.
  rewrite ! compose_print_identity in T.
  destruct (Sim1RTLToGraph.transf_program p) as [p1|e] eqn:P1; simpl in T; try discriminate.
  remember (Sim2GraphToPred.transf_program p1) as p2 eqn:P2.
  destruct (Predication.transf_program p2) as [p3|e3] eqn:P3; simpl in T; try discriminate.
  destruct (Sim4SelToRTL.transf_program p3) as [p4|e4] eqn:P4; simpl in T; try discriminate.
  unfold match_prog; simpl.
  exists p1; split. now apply Sim1RTLToGraph.transf_program_match.
  exists p2; split. rewrite P2. apply Sim2GraphToPred.transf_program_match.
  exists p3; split. now apply Sim3PredToSel.transf_program_match.
  exists p4; split. now apply Sim4SelToRTL.transf_program_match.
  now injection T.
Qed.

Theorem transl_program_correct:
  forall p tp,
  match_prog p tp ->
  forward_simulation (RTL.semantics p) (RTL.semantics tp).
Proof.
  intros p tp M. unfold match_prog, pass_match in M; simpl in M.
Ltac DestructM :=
  match goal with
    [ H: exists p, _ /\ _ |- _ ] =>
      let p := fresh "p" in let M := fresh "M" in let MM := fresh "MM" in
      destruct H as (p & M & MM); clear H
  end.
  repeat DestructM. subst tp.
  eapply compose_forward_simulations.
    eapply Sim1RTLToGraph.transf_program_correct; eassumption.
  eapply compose_forward_simulations.
    eapply Sim2GraphToPred.transf_program_correct; eassumption.
  eapply compose_forward_simulations.
    eapply Sim3PredToSel.transf_program_correct; eassumption.
    eapply Sim4SelToRTL.transf_program_correct; eassumption.
Qed.

(* This is not needed as we currently don't allow function calls. *)
Global Instance CTTransformLink : TransfLink match_prog.
Admitted.

End Transform.