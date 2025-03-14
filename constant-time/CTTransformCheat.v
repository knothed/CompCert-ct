Require Import Common Coqlib Classical Datatypes.
Require Import AST RTL Memory Registers Maps Values Events Globalenvs Smallstep Op Integers.
Require Import ListsExtra Graph GraphDual SharedTypes.
Require Import Smallstep Errors Linking.
Require Import Predication Sim1RTLToGraph Sim2GraphToPred Sim3PredToSel Sim4SelToRTL.

Parameter print_GraphRTL_fun: Z -> ident -> GraphRTL.function -> unit.
Parameter print_PredRTL_fun: Z -> ident -> PredRTL.function -> unit.

(* Here we only apply the transform to non-main functions (by comparing the signature).
   This breaks provable correctness (because we do not have a callstack in our states) but it is useful for examples. *)

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

Section Transform.

Definition transl_function' (id: ident) (f: function) : res function :=
   OK f
  @@@ time "CT1" Sim1RTLToGraph.transl_function
   @@ print (print_GraphRTL_fun 1 id)
   @@ time "CT2" Sim2GraphToPred.transl_function
   @@ print (print_PredRTL_fun 2 id)
  @@@ time "CT3" Predication.transl_function
  @@@ time "CT4" Sim4SelToRTL.transl_function.

Definition real_signature_main :=
  {| sig_args := Tint :: Tlong :: nil; sig_res := Tint; sig_cc := cc_default |}.

Definition transl_function (id: ident) (f: function) : res function :=
  if signature_eq f.(fn_sig) real_signature_main then
    OK f
  else
    transl_function' id f.

Definition transl_fundef (id: ident) (f: fundef) : res fundef := match f with
  | Internal f =>
    match transl_function id f with | OK f => OK (Internal f) | Error e => Error e end
  | External e => OK (External e)
end.
Definition transf_program (p: program) : res program := transform_partial_program2 transl_fundef (fun id g => OK g) p.

Definition match_prog (p: RTL.program) (tp: RTL.program) :=
  match_program (fun cu f tf => exists id, transl_fundef id f = OK tf) eq p tp.

Theorem transf_program_match:
  forall p tp,
  transf_program p = OK tp ->
  match_prog p tp.
Proof.
  intros. unfold transf_program in H. eapply match_transform_partial_program2; eauto.
  intros. simpl in *. now injection H0.
Qed.

Theorem transl_program_correct:
  forall prog tprog,
  match_prog prog tprog ->
  forward_simulation (RTL.semantics prog) (RTL.semantics tprog).
Proof.
  (* This of course fails because RTL has a call stack but our intermediate languages do not *)
Admitted.

Global Instance CTTransformCheatLink : TransfLink match_prog.
Admitted.

End Transform.