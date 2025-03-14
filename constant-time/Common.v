Require Import Axioms Coqlib Classical Datatypes.
Require Import Maps.

Open Scope nat.

(* nat <-> positive conversion *)
Definition Pos_to_pred_nat p := pred (Pos.to_nat p).

Lemma predsucc: forall n, Pos_to_pred_nat (Pos.of_succ_nat n) = n.
Proof. unfold Pos_to_pred_nat. extlia. Qed.

Lemma succpred: forall p, Pos.of_succ_nat (Pos_to_pred_nat p) = p.
Proof. unfold Pos_to_pred_nat. lia. Qed.

Notation "c @! n" := (PTree.get (Pos.of_succ_nat n) c) (at level 1).
Notation "c @!! n" := (PMap.get (Pos.of_succ_nat n) c) (at level 1).


(* Tactics *)

Tactic Notation "enow" tactic(x) := x; eauto; easy.

Ltac copy H := let F := fresh H in pose proof H as F.

Ltac unfold_tuples := match goal with 
  [ H: (?a, ?b) = (?c, ?d) |- _ ] => apply pair_equal_spec in H as []; try unfold_tuples
end.


Ltac irrel x y := replace x with y by apply proof_irr.

Ltac irrel_in H x y := replace x with y in H by apply proof_irr.

Ltac irrel_f f e :=
  (try replace (f _) with e by apply proof_irr) ||
  (try replace (f _ _) with e by apply proof_irr) ||
  (try replace (f _ _ _) with e by apply proof_irr) ||
  (try replace (f _ _ _ _) with e by apply proof_irr) ||
  (try replace (f _ _ _ _ _) with e by apply proof_irr) ||
  (try replace (f _ _ _ _ _ _) with e by apply proof_irr) ||
  (try replace (f _ _ _ _ _ _ _) with e by apply proof_irr) ||
  (try replace (f _ _ _ _ _ _ _ _) with e by apply proof_irr) ||
  (try replace (f _ _ _ _ _ _ _ _ _) with e by apply proof_irr) ||
  (try replace (f _ _ _ _ _ _ _ _ _ _) with e by apply proof_irr) ||
  (try replace (f _ _ _ _ _ _ _ _ _ _ _) with e by apply proof_irr) ||
  (try replace (f _ _ _ _ _ _ _ _ _ _ _ _) with e by apply proof_irr) ||
  (try replace (f _ _ _ _ _ _ _ _ _ _ _ _ _) with e by apply proof_irr) ||
  (try replace (f _ _ _ _ _ _ _ _ _ _ _ _ _ _) with e by apply proof_irr) ||
  (try replace (f _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) with e by apply proof_irr) ||
  (try replace (f _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) with e by apply proof_irr) ||
  (try replace (f _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) with e by apply proof_irr) ||
  (try replace (f _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) with e by apply proof_irr).

Ltac irrel_f_in H f e :=
  (try replace (f _) with e in H by apply proof_irr) ||
  (try replace (f _ _) with e in H by apply proof_irr) ||
  (try replace (f _ _ _) with e in H by apply proof_irr) ||
  (try replace (f _ _ _ _) with e in H by apply proof_irr) ||
  (try replace (f _ _ _ _ _) with e in H by apply proof_irr) ||
  (try replace (f _ _ _ _ _ _) with e in H by apply proof_irr) ||
  (try replace (f _ _ _ _ _ _ _) with e in H by apply proof_irr) ||
  (try replace (f _ _ _ _ _ _ _ _) with e in H by apply proof_irr) ||
  (try replace (f _ _ _ _ _ _ _ _ _) with e in H by apply proof_irr) ||
  (try replace (f _ _ _ _ _ _ _ _ _ _) with e in H by apply proof_irr) ||
  (try replace (f _ _ _ _ _ _ _ _ _ _ _) with e in H by apply proof_irr) ||
  (try replace (f _ _ _ _ _ _ _ _ _ _ _ _) with e in H by apply proof_irr) ||
  (try replace (f _ _ _ _ _ _ _ _ _ _ _ _ _) with e in H by apply proof_irr) ||
  (try replace (f _ _ _ _ _ _ _ _ _ _ _ _ _ _) with e in H by apply proof_irr) ||
  (try replace (f _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) with e in H by apply proof_irr) ||
  (try replace (f _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) with e in H by apply proof_irr) ||
  (try replace (f _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) with e in H by apply proof_irr) ||
  (try replace (f _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) with e in H by apply proof_irr).

Ltac rem f :=
  (try remember (f _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)) ||
  (try remember (f _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)) ||
  (try remember (f _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)) ||
  (try remember (f _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)) ||
  (try remember (f _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)) ||
  (try remember (f _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)) ||
  (try remember (f _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)) ||
  (try remember (f _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)) ||
  (try remember (f _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)) ||
  (try remember (f _ _ _ _ _ _ _ _ _ _ _ _ _ _)) ||
  (try remember (f _ _ _ _ _ _ _ _ _ _ _ _ _)) ||
  (try remember (f _ _ _ _ _ _ _ _ _ _ _ _)) ||
  (try remember (f _ _ _ _ _ _ _ _ _ _ _)) ||
  (try remember (f _ _ _ _ _ _ _ _ _ _)) ||
  (try remember (f _ _ _ _ _ _ _ _ _)) ||
  (try remember (f _ _ _ _ _ _ _ _)) ||
  (try remember (f _ _ _ _ _ _ _)) ||
  (try remember (f _ _ _ _ _ _)) ||
  (try remember (f _ _ _ _ _)) ||
  (try remember (f _ _ _ _)) ||
  (try remember (f _ _ _)) ||
  (try remember (f _ _)) ||
  (try remember (f _)).


(* More *)

Lemma strong_rect (P: nat -> Type):
  (forall m, (forall k : nat, k < m -> P k) -> P m) ->
  forall n, P n.
Proof.
  intros H n0; enough (H0: forall p, p <= n0 -> P p).
    - apply H0, le_n. 
    - induction n0.
    + intros. replace p with 0 by lia. apply H. lia.
    + intros. apply H. intros. apply IHn0. lia.
Qed.

Lemma strong_ind (P: nat -> Prop):
  (forall m, (forall k : nat, k < m -> P k) -> P m) ->
  forall n, P n.
Proof.
  apply strong_rect.
Qed.

Lemma list_length_ind: forall {A} xs
  (P: list A -> Prop)
  (H: forall xs, (forall l, length l < length xs -> P l) -> P xs),
  P xs.
Proof.
  intros.
  enough (I: forall l, length l <= length xs -> P l) by (apply I; lia).
  induction xs; intros; apply H; intros.
  - inv H0. lia.
  - apply IHxs. simpl in H0. lia.
Qed.