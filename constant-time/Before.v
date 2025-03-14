Require Import Axioms Common Coqlib Classical Datatypes.
Require Import ListsExtra.

Section Before.

Context {A: Type}.
Hypothesis eq_dec: forall (x y: A), {x=y} + {x<>y}.

Definition index := index eq_dec.

Variable l: list A.
Hypothesis ND: NoDup l.

Definition beforeeq x y :=
  exists i j, i <= j /\ nth_error l i = Some x /\ nth_error l j = Some y.

Definition before x y :=
  exists i j, i < j /\ nth_error l i = Some x /\ nth_error l j = Some y.

Notation "x <<= y" := (beforeeq x y) (at level 20).
Notation "x << y" := (before x y) (at level 20).

Lemma before_in: forall x y, x << y -> In x l /\ In y l.
Proof.
  intros. destruct H as [j [? [? []]]]. split.
  now apply nth_error_in in H0. now apply nth_error_in in H1.
Qed.

Lemma beforeeq_id: forall x, In x l -> x <<= x.
Proof.
  intros. destruct (index l x H). exists x0, x0.
  split; auto; split; auto.
Qed.

Lemma before_id: forall x, ~ x << x.
Proof.
  intros. case (In_dec eq_dec x l) eqn:IN.
  * destruct (index l x i). intro. unfold before in H. do 3 (destruct H). destruct H0.
    copy H0. rewrite <- H1 in H2.
    assert (x1 < length l) by now apply nth_error_len in H0.
    pose ((proj1 (NoDup_nth_error l)) ND x1 x2 H3 H2). lia.
  * intro. unfold before in H. do 3 (destruct H). destruct H0.
    apply nth_error_in in H0. auto.
Qed.

Lemma before_id_neq: forall x y,
  x << y -> x <> y.
Proof.
  intros. destruct (eq_dec x y); auto. subst. apply before_id in H. contradiction.
Qed.

Lemma before_yields_eq: forall x y,
  x << y -> x <<= y.
Proof.
  intros. destruct H as [i [j]]. exists i, j. intuition auto. lia.
Qed.

Lemma beforeeq_split: forall x y,
  x <<= y -> x = y \/ x << y.
Proof.
  intros. case (eq_dec x y) eqn:E. auto.
  right. destruct H as [i [j [ij [X Y]]]].
  exists i, j. case (Nat.eq_dec i j); intuition auto. congruence. lia.
Qed.

Lemma before_unique: forall x y,
  x << y -> ~ y << x.
Proof.
  intros. intro. destruct H0 as [i [j [LT [N1 N2]]]]. destruct H as [j' [i' [LT' [N2' N1']]]].
  copy N1. rewrite <- N1' in N1. apply NoDup_nth_error in N1.
  copy N2. rewrite <- N2' in N2. apply NoDup_nth_error in N2.
  lia. auto. now apply nth_error_len in N3. auto. now apply nth_error_len in N0.
Qed.

Lemma beforeeq_unique: forall x y,
  x << y -> ~ y <<= x.
Proof.
  intros. intro. apply beforeeq_split in H0 as [].
  * apply before_id_neq in H. symmetry in H0. contradiction.
  * apply before_unique in H. contradiction.
Qed. 

Lemma beforeeq_swap: forall x y,
  x <<= y -> ~ y << x.
Proof.
  intros. apply beforeeq_split in H as [].
  * subst. now apply before_id.
  * now apply before_unique.
Qed.

Lemma beforeeq_both: forall x y,
  x <<= y -> y <<= x -> x = y.
Proof.
  intros. apply beforeeq_split in H as [], H0 as []; auto. apply before_unique in H. contradiction.
Qed.

Lemma beforeeq_trans: forall x y z,
  x <<= y -> y <<= z -> x <<= z.
Proof.
  intros. destruct H as [i [j [? [? ?]]]], H0 as [k [m [? [? ?]]]].
  replace j with k in *.
  2: { copy H3. rewrite <- H2 in H3. apply NoDup_nth_error in H3; auto. now apply nth_error_len in H5. }
  exists i, m. intuition auto. lia.
Qed.

Lemma beforeeq_trans_2: forall x y z,
  x << y -> y <<= z -> x << z.
Proof.
  intros. destruct H as [i [j [? [? ?]]]], H0 as [k [m [? [? ?]]]].
  replace j with k in *.
  2: { copy H3. rewrite <- H2 in H3. apply NoDup_nth_error in H3; auto. now apply nth_error_len in H5. }
  exists i, m. intuition lia.
Qed.

Lemma before_trans: forall x y z,
  x << y -> y << z -> x << z.
Proof.
  intros. eapply beforeeq_trans_2; eauto. now apply before_yields_eq.
Qed.

Lemma before_dec: forall x y,
  x <> y -> In x l -> In y l ->
  {x << y} + {y << x}.
Proof.
  intros.
  destruct (index l x H0), (index l y H1).
  destruct (lt_eq_lt_dec x0 x1) as [[|]|].
  * left. now exists x0, x1.
  * congruence.
  * right. now exists x1, x0. 
Qed.

Lemma beforeeq_dec: forall x y,
  In x l -> In y l -> {x << y} + {y <<= x}.
Proof.
  intros. case (eq_dec x y) eqn:?.
  right. rewrite e. now apply beforeeq_id.
  clear Heqs. apply before_dec in n as []; auto. right. now apply before_yields_eq.
Qed.

Hint Resolve beforeeq_id beforeeq_split beforeeq_swap before_yields_eq
             before_trans beforeeq_trans before_unique before_dec
             : core.

Notation "x <<= y" := (beforeeq x y) (at level 20).
Notation "x << y" := (before x y) (at level 20).

Definition smaller_in (x: {v: A | In v l}) (y: {v: A | In v l}) : {(!x) <<= (!y)} + {(!y) <<= (!x)}.
Proof.
  intros. destruct x as [x X], y as [y Y]. destruct (eq_dec x y).
  left. subst. simpl. now apply beforeeq_id.
  destruct (before_dec x y); auto.
Defined.

Definition min_in: forall (xs: list {v: A | In v l}), xs <> nil ->
                   {s: {v: A | In v l} | In s xs /\ forall x, In x (map (fun a => !a) xs) -> (!s) <<= x}.
refine (fix f (xs: list {v: A | In v l}) := _).
Proof.
  intros. induction xs.
  * intuition auto.
  * destruct xs.
   + exists a. split. apply in_eq. intros. simpl in H0. destruct H0; try contradiction. subst. apply beforeeq_id. destruct a. now simpl.
   + pose proof (IHxs ltac:(congruence)) as [m X].
     epose proof (smaller_in a m). destruct H0.
     - exists a. destruct a in *. split. apply in_eq.
       intros. destruct H0. rewrite H0. apply beforeeq_id; now rewrite <- H0. simpl. destruct H0. subst. destruct X.
       pose proof (H1 (!s) ltac:(now left)). apply beforeeq_trans with (y:=!m); auto.
       destruct X. pose proof (H2 x0 ltac:(now apply in_cons)). apply beforeeq_trans with (y:=!m); auto.
     - exists m. split. now apply in_cons. intros. now destruct H0; [subst | apply X].
Defined.

(* From Prop to Set *)

Lemma _before_unfold: forall x y,
  x <<= y -> (exists i, nth_error l i = Some x) /\ (exists j, nth_error l j = Some y).
Proof.
  intros. destruct H. destruct H. split. now exists x0. now exists x1.
Qed.

Lemma _before_unfold_lt: forall x y i j,
  x << y ->
  nth_error l i = Some x ->
  nth_error l j = Some y ->
  i < j.
Proof.
  intros. destruct H as [? [? [? []]]].
  assert (x0 = i) by enow eapply index_same.
  assert (x1 = j) by enow eapply index_same.
  lia.
Qed.

Lemma _beforeeq_unfold_le: forall x y i j,
  x <<= y ->
  nth_error l i = Some x ->
  nth_error l j = Some y ->
  i <= j.
Proof.
  intros. destruct H as [? [? [? []]]].
  assert (x0 = i) by enow eapply index_same.
  assert (x1 = j) by enow eapply index_same.
  lia.
Qed.

Lemma nth_error_find_single: forall A (l: list A) (ND: NoDup l) (eq_dec: forall (x y: A), {x=y} + {x<>y}) x,
  (exists i, nth_error l i = Some x) ->
  { i: nat | nth_error l i = Some x }.
Proof.
  intros. induction l0. exfalso. destruct H. now rewrite nth_error_nil in H.
  case (eq_dec0 a x) eqn:?.
  * exists 0. simpl. now subst.
  * apply NoDup_cons_iff in ND0 as []. apply IHl0 in H1. destruct H1. now exists (S x0).
    destruct H. case x0 in *. simpl in H. congruence. now exists x0.
Qed.

Lemma before_to_set: forall x y,
  x << y -> { '(i, j): nat * nat | i < j /\ nth_error l i = Some x /\ nth_error l j = Some y }.
Proof.
  intros. copy H. apply before_yields_eq in H. apply _before_unfold in H as [].
  apply nth_error_find_single in H as []; auto.
  apply nth_error_find_single in H1 as []; auto.
  exists (x0,x1). split; auto.
  enow eapply _before_unfold_lt.
Qed.

Lemma beforeeq_to_set: forall x y,
  x <<= y -> { '(i, j): nat * nat | i <= j /\ nth_error l i = Some x /\ nth_error l j = Some y }.
Proof.
  intros. copy H. apply _before_unfold in H as [].
  apply nth_error_find_single in H as []; auto.
  apply nth_error_find_single in H1 as []; auto.
  exists (x0,x1). split; auto.
  enow eapply _beforeeq_unfold_le.
Qed.

End Before.

Notation "x <<= y 'in' l" := (beforeeq l x y) (at level 20).
Notation "x << y 'in' l" := (before l x y) (at level 20).

Lemma before_rev: forall A x y (l: list A),
  x << y in l <-> y << x in rev l.
Proof.
  assert (forall A x y (l: list A), x << y in l -> y << x in rev l). {
    intros. destruct H as [ix [iy [? []]]].
    assert (iy < length l) by (eapply nth_error_len; eauto).
    rewrite rev_nth_error in H0, H1; try eapply nth_error_len; eauto.
    exists (length l - S iy), (length l - S ix).
    repeat split; auto; lia.
  }
  split; [ apply H | replace l with (rev (rev l)) at 2 by apply rev_involutive; apply H ].
Qed.

Lemma beforeeq_rev: forall A (eq_dec: forall x y: A, {x=y} + {x<>y}) x y (l: list A),
  x <<= y in l <-> y <<= x in rev l.
Proof.
  intros A eq_dec.
  assert (forall x y (l: list A), x <<= y in l -> y <<= x in rev l). {
    intros. assert (In y l) by (destruct H as [? [? [? []]]]; eapply nth_error_in; eauto).
    apply (beforeeq_split eq_dec) in H as []; [ now rewrite H; apply (beforeeq_id eq_dec); apply in_rev in H0 | now apply before_yields_eq; apply before_rev in H ].
  }
  split; [ apply H | replace l with (rev (rev l)) at 2 by apply rev_involutive; apply H ].
Qed.


Definition min_in_nat := min_in Nat.eq_dec.
Arguments min_in _ _ _ _ _ _: simpl nomatch. 
Arguments min_in_nat _ _ _ _: simpl nomatch. 

Lemma min_in_nat_proof_irr: forall (l: list nat) (ND1 ND2: NoDup l) (xs: list {v: nat | In v l}) nn1 nn2,
  !(!(min_in_nat l ND1 xs nn1)) = !(!(min_in_nat l ND2 xs nn2)).
Proof.
  intros. irrel nn1 nn2. now irrel ND1 ND2.
Qed.

Lemma min_in_nat_element_proof_irr: forall (l: list nat) (ND1 ND2: NoDup l) (a1 a2: {v: nat | In v l}) (xs: list {v: nat | In v l}) nn1 nn2,
  !a1 = !a2 -> !(!(min_in_nat l ND1 (a1::xs) nn1)) = !(!(min_in_nat l ND2 (a2::xs) nn2)).
Proof.
  intros.
  intros. repeat destruct min_in_nat. destruct a, a0. simpl in *. remember (map (fun a => !a) xs) as xs'. destruct i, i0;
  try assert (In (!x0) xs') by (rewrite Heqxs'; now apply in_map); try assert (In (!x) xs') by (rewrite Heqxs'; now apply in_map); subst;
  try eapply (beforeeq_both Nat.eq_dec); eauto.
Qed.