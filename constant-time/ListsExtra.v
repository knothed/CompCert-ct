Require Import Common Coqlib Classical Datatypes Maps.

Open Scope nat.

(*** Additional lemmata about lists. ***)

(*** NTH ***)

Lemma in_nth_err: forall A x (l: list A),
  In x l <-> exists n, nth_error l n = Some x.
Proof.
  intros. split.
  - induction l. intro. contradiction H.
    intro. apply in_inv in H. destruct H.
    + exists O. simpl. now rewrite H.
    + destruct (IHl H) as [n F]. exists (S n). now simpl.
  - intros []. eapply nth_error_in. eauto.
Qed.

Lemma nth_or_error: forall A d n (l: list A), n < length l -> Some (nth n l d) = nth_error l n.
Proof.
  intros A d n l. generalize dependent n. induction l; intros.
   - simpl in H. lia.
   - destruct n. auto. simpl in H. apply Nat.succ_lt_mono in H. simpl. auto.
Qed.

Lemma nth_error_len: forall A n x (l: list A), nth_error l n = Some x -> n < length l.
Proof.
  intros. generalize dependent n. induction l.
    - intros. now rewrite nth_error_nil in H.
    - intros. destruct n. simpl. lia.
      simpl. rewrite <- Nat.succ_lt_mono. apply (IHl n). now simpl in H.
Qed.

Lemma in_nth: forall A x d (l: list A),
  In x l -> exists n, nth n l d = x /\ n < length l.
Proof.
  intros. apply in_nth_err in H as [n]. apply nth_error_len in H as L. rewrite <- nth_or_error with (d:=d) in H.
  - exists n. now injection H.
  - now apply nth_error_len in H.
Qed.

Lemma nth_add: forall A (l1 l2: list A) n x,
  (forall j, j < n -> nth_error l1 j = nth_error l2 j) ->
  length l1 = n ->
  nth_error l2 n = Some x ->
  forall j, j < S n -> nth_error (l1++x::nil) j = nth_error l2 j.
Proof.
  intros. case (Nat.eq_dec j n) eqn:N.
  * rewrite nth_error_app2; try lia. rewrite e, H0. rewrite Nat.sub_diag. now simpl.
  * rewrite nth_error_app1; try lia. apply H. lia.
Qed.

Lemma firstn_nth: forall A (l: list A) i n,
  i < n -> nth_error l i = nth_error (firstn n l) i.
Proof.
  induction l. intros. now rewrite firstn_nil.
  intros. case i eqn:I; case n eqn:N; try lia. rewrite firstn_cons. now simpl.
  rewrite firstn_cons. simpl. apply IHl. lia.
Qed.

Lemma firstn_app_nth: forall A (l: list A) d n,
  (S n) <= length l ->
  firstn n l ++ nth n l d :: nil = firstn (S n) l.
Proof.
  induction l.
  * intros. simpl in H. lia.
  * intros. case n eqn:N. now simpl.
    rewrite firstn_cons. simpl nth. rewrite <- app_comm_cons. rewrite IHl; auto. simpl in H. lia.
Qed.

Lemma rev_nth_error: forall A (l: list A) n,
  n < length l ->
  nth_error l n = nth_error (rev l) (length l - S n).
Proof.
  intros.
  repeat erewrite <- nth_or_error; try rewrite rev_length; try lia.
  apply f_equal. replace l with (rev (rev l)) at 1; [| apply rev_involutive ]. replace (length l) with (length (rev l)); [| apply rev_length ]. apply rev_nth. now rewrite rev_length.
  Unshelve. destruct l; [simpl in H; lia | exact a].
Qed.

Lemma map_equal_nth: forall A B C (f: A -> C) (g: B -> C) (l1: list A) (l2: list B),
  length l1 = length l2 ->
  (forall i d1 d2, i < length l1 -> f (nth i l1 d1) = g (nth i l2 d2)) ->
  map f l1 = map g l2.
Proof.
  induction l1, l2; intros.
  * auto.
  * simpl in H; congruence.
  * simpl in H; congruence.
  * simpl.
    replace (g b) with (f a) by (epose (H0 0 _ _ ltac:(auto)); now simpl in e).
    rewrite IHl1 with (l2:=l2); auto.
    intros. now epose (H0 (S i) d1 d2 ltac:(auto)).
  Unshelve.
  all: auto; simpl; lia.
Qed.

(*** LAST ***)

Lemma last_cons: forall A d l' l (ls: list A), last (l::ls) d = last (l'::l::ls) d.
Proof.
  induction ls. auto. simpl. destruct ls; auto.
Qed.

Lemma last_nth: forall A d l (ls: list A), last (l::ls) d = nth (length ls) (l::ls) d.
Proof.
  intros. induction ls. auto. destruct ls; auto.
Qed.

Lemma last_In: forall A l (d: A), l <> nil -> In (last l d) l.
Proof.
  intros. induction l. easy. case l in *. enow simpl. assert (a0 :: l <> nil) by easy.
  apply IHl in H0. simpl in *. case l in *. auto. enow case H0.
Qed.

(*** FILTER ***)

Lemma filter_same:
  forall A f (l: list A),
  (forall x, In x l -> f x = true) ->
  filter f l = l.
Proof.
  intros. induction l. auto.
  simpl. epose proof (H a _). rewrite H0. epose proof (IHl _). rewrite H1. auto.
  Unshelve. apply in_eq. intros. now epose proof (H x _). Unshelve. now apply in_cons.
Qed.

Lemma filter_nil:
  forall A f (l: list A),
  (forall x, In x l -> f x = false) ->
  filter f l = nil.
Proof.
  intros. induction l. auto.
  simpl. epose proof (H a _). rewrite H0. epose proof (IHl _). auto.
  Unshelve. apply in_eq. intros. now epose proof (H x _). Unshelve. now apply in_cons.
Qed.

Lemma filter_filter: forall A f g h (l: list A),
  (forall x, f x = g x && h x) ->
  filter f l = filter g (filter h l).
Proof.
  intros. induction l. auto.
  simpl.
  case h eqn:Ha, (g a) eqn:Ga; pose proof (H a) as Fa; rewrite Ha, Ga in Fa; simpl in Fa.
  1-2: simpl; rewrite Fa, Ga; now rewrite IHl.
  1-2: simpl; rewrite Fa; apply IHl.
Qed.

Lemma filter_length_le: forall A f (l: list A),
  length (filter f l) <= length l.
Proof.
  intros. induction l. auto. simpl. case (f a); simpl; lia.
Qed.

Lemma filter_length_eq: forall A f (l: list A),
  length (filter f l) = length l ->
  filter f l = l.
Proof.
  intros. induction l. auto.
  simpl in *. case (f a) eqn:?.
  + f_equal. enow apply IHl.
  + pose proof (filter_length_le A f l). lia.
Qed.

Lemma filter_length_neq: forall A f (l: list A),
  length (filter f l) <> length l ->
  exists x, In x l /\ f x = false.
Proof.
  intros. induction l. simpl in H. lia.
  case (f a) eqn:?.
  * simpl in H. rewrite Heqb in H. simpl in H. assert (length (filter f l) <> length l) by lia. apply IHl in H0 as [? []].
    exists x. split. now apply in_cons. auto.
  * exists a. split. now apply in_eq. auto.
Qed. 

(*** INDUCTION ***)

Lemma list_ind_rev : forall {A} (P : list A -> Prop),
  P nil ->
  (forall l x, P l -> P (l ++ x::nil)) ->
  forall l, P l.
Proof.
  intros. remember (rev l) as revl. generalize dependent l.
  induction revl; intros; apply (f_equal (@rev A)) in Heqrevl; rewrite rev_involutive in Heqrevl; simpl in Heqrevl.
  * destruct l; [apply H | congruence].
  * rewrite <- Heqrevl. apply H0, IHrevl. now rewrite rev_involutive.
Qed.

(*** INDEX ***)

Notation "[ e ]" := (exist _ e _).
Notation "[ x X ]" := (exist _ x X).
Notation "! x" := (proj1_sig x) (at level 10).

Section Index.

Context {A: Type}.
Hypothesis eq_dec: forall (x y: A), {x=y} + {x<>y}.

Definition index: forall (l: list A) (x: A), In x l -> { n: nat | nth_error l n = Some x }.
refine (fix f (l: list A) (x: A) (inxl: In x l) := match l, inxl return { n: nat | nth_error l n = Some x } with
  | nil, inxl => match (in_nil inxl) with end
  | y::ys, _ => if eq_dec x y then [0] else let i := f ys x _ in [S (!i)]
end).
* now subst.
* unfold proj1_sig. now destruct i.
Unshelve. destruct inxl; [congruence|auto].
Defined.

Lemma index_nth: forall (l: list A) i d inl,
  i < length l ->
  NoDup l ->
  !(index l (nth i l d) inl) = i.
Proof.
  intros. destruct index. simpl. rewrite nth_or_error in e; auto.
  rewrite NoDup_nth_error in H0. symmetry. symmetry in e. exact (H0 i x H e).
Qed.

Lemma nth_index: forall (l: list A) x d inl,
  nth (!(index l x inl)) l d = x.
Proof.
  intros. destruct index. now apply nth_error_nth.
Qed.

Lemma index_len: forall (l: list A) x ix, !(index l x ix) < length l.
Proof.
  intros. destruct index. simpl. now apply nth_error_len in e.
Qed.

Lemma index_same: forall (l: list A) i j x,
  NoDup l -> nth_error l i = Some x -> nth_error l j = Some x -> i = j.
Proof.
  intros. rewrite <- H0 in H1. eapply NoDup_nth_error; eauto; now apply nth_error_len in H0.
Qed.

End Index.

Definition index_nat := index Nat.eq_dec.
Arguments index _ _ _ _ _: simpl nomatch. 
Arguments index_nat _ _ _: simpl nomatch.

(*** MAP_EXTRA ***)

Definition map_extra {A} {B}: forall (l: list A) (P: B -> Prop) (f: A -> B) (g: {x: A | In x l} -> {x: B | P x}), (forall x, !(g x) = f (!x)) ->
  {r: list {x: B | P x} | map (@proj1_sig B P) r = map f l}.
refine (fix map_extra (l: list A) (P: B -> Prop) (f: A -> B) (g: {x: A | In x l} -> {x: B | P x}) := _).
Proof.
  intros. induction l.
  * exists nil. now simpl.
  * epose (g' := _ : {x: A | In x l} -> {x: B | P x}).
    Unshelve. 2: { intro. destruct X. assert (In x (a::l)) by now apply in_cons. exact (g (exist _ x H0)). }  
    assert (forall x: {x: A | In x l}, !(g' x) = f (!x)). { intro. destruct x. assert (In x (a::l)) by now apply in_cons. apply H. }
    pose proof (map_extra l P f g' H0) as [m M].
    epose ([a]: {x: A | In x (a::l)}) as a'. Unshelve. 2: { simpl; now left. }
    exists (g a' :: m). simpl. specialize H with a'. rewrite M, H at 1. now simpl.
Qed.

Lemma mapid: forall A (l: list A), map id l = l.
Proof.
  induction l. auto. simpl. rewrite IHl. now unfold id.
Qed.

Definition map_extra_id {A} (l: list A) (P: A -> Prop) (g: forall x, In x l -> P x) : {r: list {x: A | P x} | map (@proj1_sig A P) r = l}.
Proof.
  epose proof (map_extra l P id (fun H => let (x,i) := H in (exist P x (g x i))) _) as [r R].
  exists r. rewrite R. apply mapid. Unshelve. now intros [].
Defined.


Lemma map_extra_length: forall A B (l: list A) P (f: A -> B) g N,
  length l = length (!(map_extra l P f g N)).
Proof.
  intros. remember (map_extra l P f g N) as s. destruct s. simpl.
  clear Heqs. apply (f_equal (@length B)) in e. repeat rewrite map_length in e. now symmetry.
Qed.


Lemma map_extra_id_length: forall A (l: list A) P g,
  length l = length (!(map_extra_id l P g)).
Proof.
  intros. remember (map_extra_id l P g) as s. destruct s. simpl.
  clear Heqs. apply (f_equal (@length A)) in e. repeat rewrite map_length in e. now symmetry.
Qed.

Lemma map_extra_id_nonnil: forall A (l: list A) P g,
  l <> nil -> !(map_extra_id l P g) <> nil.
Proof.
  intros. destruct l eqn:L. auto. eremember (map_extra_id _ _ _). destruct s. simpl. destruct x. auto. congruence. 
Qed.

Lemma map_extra_id_In: forall A (l: list A) x P g a,
  In (exist P x a) (!(map_extra_id l P g)) -> In x l.
Proof.
  intros. destruct (map_extra_id l P g). simpl in *.
  apply in_map with (f:=proj1_sig (P:=P)) in H. simpl in H. now rewrite e in H.
Qed.

Lemma map_extra_id_In_rev: forall A (eq_dec: forall (x y: A), {x=y} + {x<>y}) (l: list A) x P g,
  In x l -> exists x', In x' (!(map_extra_id l P g)) /\ !x' = x.
Proof.
  intros. remember (!(map_extra_id l P g)) as l'. destruct (index eq_dec l x H) as [ix].
  assert A as d. { destruct l. contradiction. exact x. }
  assert {x0:A | P x0} as d'. { destruct map_extra_id. destruct x0. simpl in e0. subst. contradiction. exact s. }
  remember (nth ix l' d') as x'. exists x'.
  assert (ix < length l) by now apply nth_error_len in e. assert (ix < length l'). { destruct map_extra_id. rewrite <- e0 in H0. rewrite map_length in H0. simpl in *. now subst. }
  split.
  * rewrite Heqx'. apply nth_In; auto.
  * apply nth_or_error with (d:=d') in H1. rewrite <- Heqx' in H1. destruct map_extra_id. simpl in *. rewrite Heql' in H1. rewrite <- e0 in e.
    symmetry in H1. apply map_nth_error with (f:=proj1_sig(P:=P)) in H1. rewrite e in H1. now injection H1.
Qed.

Lemma map_extra_id_nth: forall A (eq_dec: forall (x y: A), {x=y} + {x<>y}) (l: list A) P g i d,
  i < length l ->
  !(nth i (!(map_extra_id l P g)) d) = nth i l (!d).
Proof.
  intros. destruct map_extra_id. simpl. now rewrite <- e, map_nth.
Qed.

(*** TO TREE ***)

Fixpoint to_tree' {A} (i: nat) (l: list A) (t: PTree.t A): PTree.t A :=
  match l with 
  | nil => t
  | x::xs => to_tree' (i+1) xs (PTree.set (Pos.of_succ_nat i) x t)
  end.

Definition to_tree {A} (l: list A): PTree.t A := to_tree' 0 l (PTree.empty A).

Lemma to_tree'_above: forall A (t: PTree.t A) i j l,
  i < j ->
  (to_tree' j l t) @! i = t @! i.
Proof.
  intros. generalize dependent t. generalize dependent j. induction l. auto.
  simpl. intros. rewrite IHl, PTree.gso. auto. lia. lia.
Qed.

Lemma to_tree'_spec: forall A (l: list A) t i j,
  i >= j ->
  (forall i, i >= j -> t @! i = None) ->
  (to_tree' j l t) @! i = (nth_error l (i-j)).
Proof.
  intros. generalize dependent t. generalize dependent i. generalize dependent j. induction l.
  * intros. now rewrite H0, nth_error_nil.
  * simpl. intros. case (Nat.eq_dec i j) eqn:?.
    + rewrite e, to_tree'_above, PTree.gss, Nat.sub_diag; auto; lia.
    + rewrite IHl. remember (i-(j+1)) as x. replace (i-j) with (S x) by lia. auto. lia.
    { intros. rewrite PTree.gso, H0; auto; lia. }
Qed.

Lemma to_tree_spec: forall A (l: list A) i,
  (to_tree l) @! i = (nth_error l i).
Proof.
  intros. unfold to_tree. rewrite to_tree'_spec.
  * now replace (i-0) with i by lia.
  * lia.
  * auto.
Qed.