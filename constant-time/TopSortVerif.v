Require Import Common Coqlib Classical Datatypes List Permutation.
Require Import Graph Before ListsExtra.

(* External top sort *)
Parameter calc_top_sort: G -> list nat.

Fixpoint weak_idx i x (idx: list nat): option nat := match idx with
  | nil => None
  | l :: ls => if l =? x then Some i else weak_idx (S i) x ls
end.

Definition weak_before x y (idx: list nat): bool := match (weak_idx 0 x idx, weak_idx 0 y idx) with
  | (Some ix, Some iy) => ix <? iy
  | _ => false
end.

Lemma weak_idx_shift: forall i x l ix,
  weak_idx (S i) x l = Some (S ix) ->
  weak_idx i x l = Some ix.
Proof.
  intros. generalize dependent i. induction l. easy.
  intros. simpl in *. case (a =? x) eqn:?.
  * f_equal. injection H. lia.
  * now apply IHl. 
Qed.

Lemma weak_idx_ge: forall i x l ix,
  weak_idx i x l = Some ix ->
  ix >= i.
Proof.
  intros. generalize dependent i. induction l. easy.
  intros. simpl in H. case (a =? x) in H. injection H; lia. apply IHl in H. lia.
Qed.

Lemma weak_idx_red: forall x ix l ls,
  weak_idx 0 x (l::ls) = Some ix ->
  (ix = 0 /\ x = l) \/
  exists ix', ix = S ix' /\ weak_idx 0 x ls = Some ix'.
Proof.
  intros. simpl in H. case (l =? x) eqn:?.
  * left. split. congruence. now apply Nat.eqb_eq in Heqb.
  * right. exists (ix-1). copy H. apply weak_idx_ge in H. split. lia.
    replace ix with (S (ix-1)) in H0 by lia. now apply weak_idx_shift.
Qed.

Lemma weak_idx_spec: forall x ix idx,
  weak_idx 0 x idx = Some ix ->
  nth_error idx ix = Some x.
Proof.
  intros. generalize dependent ix. induction idx in *. easy.
  intros. apply weak_idx_red in H as [[]|[]]. subst. auto.
  * destruct H. apply IHidx in H0. now subst.
Qed.

Lemma weak_before_spec: forall x y idx,
  weak_before x y idx = true ->
  x << y in idx.
Proof.
  unfold before, weak_before. intros.
  do 2 (case weak_idx eqn:? in H; try congruence).
  exists n, n0. repeat split.
  * now apply Nat.ltb_lt.
  * now apply weak_idx_spec.
  * now apply weak_idx_spec.
Qed.

Definition top_sort_correct (n: nat) (g: G) (idx: list nat): bool :=
  andb
    (length idx =? n)
  (andb
    (forallb (fun v => existsb (fun v' => v =? v') idx) (seq 0 n))
    (forallb (fun e => weak_before (fst e) (snd e) idx) g.(es))).

Definition top_sort_correct_dec (n: nat) (g: G) (idx: list nat):
  {top_sort_correct n g idx = true} + {~(top_sort_correct n g idx = true)}.
Proof.
  case (top_sort_correct n g idx) eqn:?; auto.
Qed.

Lemma top_sort_alt_char: forall n g idx,
  g.(vs) = seq 0 n ->
  length idx = n ->
  NoDup g.(vs) ->
  (forall m, m < n -> In m idx) ->
  (forall u v, In (u,v) g.(es) -> u << v in idx) ->
  top_sort g idx.
Proof.
  intros. assert (Permutation (vs g) idx). {
    apply NoDup_Permutation_bis; auto. now rewrite H0, H, seq_length.
    unfold incl. intros. rewrite H, in_seq in H4. apply H2. lia. }
  constructor. auto.
  * intros. intro. destruct H6. apply H3 in H6. apply (beforeeq_unique Nat.eq_dec) in H5; auto.
    enow eapply Permutation_NoDup.
Qed.

Lemma top_sort_correct_spec: forall n g idx,
  g.(vs) = seq 0 n ->
  top_sort_correct n g idx = true ->
  top_sort g idx.
Proof.
  intros. apply andb_prop in H0 as []. apply andb_prop in H1 as [].
  rewrite Nat.eqb_eq in H0. rewrite forallb_forall in H1, H2.    
  eapply top_sort_alt_char; eauto.
  * now destruct g.
  * intros. assert (In m (seq 0 n)) by (apply in_seq; lia). apply H1 in H4. apply existsb_exists in H4 as [? []].
    apply Nat.eqb_eq in H5. now subst.
  * intros. apply H2 in H3. now apply weak_before_spec.
Qed.