Require Import Common Coqlib Classical Datatypes BinPos.
Require Import Permutation.
Require Import ListsExtra Before.
Require Import Graph.

Definition flip '(a,b): (nat*nat) := (b,a).

Lemma flip_flip: forall x, flip (flip x) = x.
Proof.
  now destruct x.
Qed.

Definition dual (g: G) : G :=
  mkG (vs g) (nodup g) (map flip (es g)).

Lemma dual_dual: forall g, dual (dual g) = g.
Proof.
  destruct g. unfold dual, Graph.vs, Graph.es, Graph.nodup. rewrite map_map. replace es with (map id es) at 2; try apply map_id.
  rewrite map_ext with (g:=id); [ auto | apply flip_flip ].
Qed.

Lemma dual_vertex: forall g v,
  vertex g v <-> vertex (dual g) v.
Proof.
  now unfold vertex, dual, vs.
Qed.

Lemma dual_edge: forall g v w,
  v → w in g <-> w → v in dual g.
Proof.
  unfold edge, dual, es, vertex, vs.
  intros. split; intro; destruct H, H0.
  * repeat split; auto. change (w,v) with (flip (v,w)). now apply in_map.
  * repeat split; auto. change (v,w) with (flip (w,v)). apply list_in_map_inv in H as [? []]. now rewrite H, flip_flip.
Qed.

Lemma dual_trace: forall g v w t,
  v →(t)→* w in g <-> w →(rev t)→* v in dual g.
Proof.
  assert (forall g v w t, v →(t)→* w in g -> w →(rev t)→* v in dual g). {
    intros. generalize dependent v. generalize dependent w. induction t.
    * intros; inv H.
    * intros; inv H.
    + now constructor.
    + apply IHt in H5. apply dual_edge in H4. now apply trace_right with v0.
  }
  split.
  * apply H.
  * replace t with (rev (rev t)) at 2 by apply rev_involutive.
    replace g with (dual (dual g)) at 2 by apply dual_dual.
    apply H.
Qed.

Lemma dual_path: forall g v w,
  v →* w in g <-> w →* v in dual g.
Proof.
  split; intro.
  * apply path_trace in H as []. now apply dual_trace, trace_path in H.
  * apply path_trace in H as []. apply dual_trace, trace_path in H. now rewrite dual_dual in H.
Qed.

Lemma dual_succ_pred: forall g v,
  vertex g v ->
  successors g v = predecessors (dual g) v.
Proof.
  intros. unfold successors, predecessors, dual at 4, es at 2.
  induction g.(es); auto.
  destruct a. simpl. destruct (v =? n).
  * destruct (vertex_dec g n0), (vertex_dec (dual g) n0);
    [ simpl; now rewrite IHl | rewrite dual_vertex in v0; contradiction | rewrite <- dual_vertex in v0; contradiction | now simpl ].
  * now simpl.
Qed.

Lemma dual_pred_succ: forall g v,
  vertex g v ->
  predecessors g v = successors (dual g) v.
Proof.
  intros. now rewrite dual_succ_pred, dual_dual; [| apply dual_vertex in H ].
Qed.

(*** START + EXIT VERTICES ***)

Section TopSort_Start_Exit.

Definition is_start g (v: V) : Prop := vertex g v /\ predecessors g v = nil.

Definition is_exit g (v: V) : Prop := vertex g v /\ successors g v = nil.

Lemma dual_start_exit: forall g v, is_start g v <-> is_exit (dual g) v.
Proof.
  intros. split; intro.
  * destruct H. now split; [apply dual_vertex in H | rewrite dual_pred_succ in H0].
  * destruct H. now split; [now apply dual_vertex in H | rewrite dual_pred_succ].
Qed.

Lemma dual_top_sort: forall g idx, top_sort g idx <-> top_sort (dual g) (rev idx).
Proof.
  assert (forall g idx, top_sort g idx -> top_sort (dual g) (rev idx)). {
    intros. destruct H. split.
    * unfold dual, vs in *; apply Permutation_trans with idx; auto; apply Permutation_rev.
    * intros. apply (beforeeq_rev nat Nat.eq_dec) in H1. apply H0 in H1.
      intro. apply dual_edge in H2. contradiction.
  }
  split.
  * apply H.
  * replace g with (dual (dual g)) at 2 by apply dual_dual.
    replace idx with (rev (rev idx)) at 2 by apply rev_involutive.
    apply H.
Qed.

Variable g: G.
Variable idx: list V.
Hypothesis IDX: top_sort g idx.

Let n := length g.(vs).
Hypothesis NN: n > 0.

Lemma top_sort_len: length idx = n.
Proof.
  intros. destruct IDX. rewrite Permutation_length with (l':=g.(vs)). auto. now apply Permutation_sym.
Qed.

Lemma top_sort_last_exit: forall d, is_exit g (nth (n-1) idx d).
Proof.
  intros. remember (nth (n-1) idx d) as last eqn:HL.
  split.
  * copy IDX. apply idx_in with (x:=last) in IDX0. apply IDX0. apply (f_equal Some) in HL. rewrite nth_or_error in HL.
    symmetry in HL. now apply nth_error_in in HL. rewrite top_sort_len. lia.
  * assert (n-1 < length idx) by (rewrite top_sort_len; lia); apply nth_or_error with (d:=d) in H; rewrite <- HL in H.
    assert (vertex g last) by (symmetry in H; apply nth_error_in in H; enow eapply idx_in with (x:=last) in H).
    enough (forall v, vertex g v -> ~ last → v in g) by (destruct successors eqn:S; auto; assert (last → v in g) by (apply successors_spec; auto; rewrite S; apply in_eq); apply H1 in H2; [contradiction | autopath]).
    intros. apply get_idx_in with (x:=v) (idx:=idx) in H1 as [ix]; auto.
    destruct IDX. apply H2. unfold beforeeq. exists ix, (n-1); repeat split; auto. apply nth_error_len in e; rewrite top_sort_len in e; auto. lia.
Qed.

Lemma top_sort_path_to_exit:
  forall v, vertex g v ->
  exists e, is_exit g e /\ v →* e in g.
Proof.
  intros. 
  assert (In v idx) by (enow eapply idx_in). destruct (index_nat idx v H0) as [i]. assert (i<n) by (apply nth_error_len in e; now rewrite <- top_sort_len). copy e. apply nth_error_nth with (d:=0) in e.   
  pose (n-i) as ni. replace i with (n-ni) in * by lia. generalize dependent v. induction ni using strong_ind.
  intros. destruct (successors g v) eqn:S.
  * exists v. repeat split; auto; autopath.
  * assert (v → v0 in g) by (apply successors_spec; auto; rewrite S; apply in_eq).
    assert (v << v0 in idx) by now apply edge_before with (idx:=idx) in H3.
    assert (In v0 idx) by (enow eapply idx_in).
    destruct H4 as [i' [j [? []]]]. 
    assert (n-ni = i'). { rewrite <- H6 in e0 at 1. apply NoDup_nth_error in e0; try eapply top_sort_nodup; eauto. rewrite top_sort_len. lia. }
    pose (n-j) as nj. assert (j<n) by (now apply nth_error_len in H7; rewrite <- top_sort_len). replace j with (n-nj) in * by lia.
    apply H in H7 as [ex []]; auto; try lia; try autopath; try now apply nth_error_nth.
    exists ex. split; auto; autopath.
Qed.

Lemma postdom_path:
  forall v w exit,
  (forall v, v = exit <-> is_exit g v) ->
  postdom g exit w v ->
  v →* w in g.
Proof.
  intros. assert (vertex g v) by now destruct H0. apply top_sort_path_to_exit in H1 as [? []].
  apply H in H1. subst x. enow eapply postdom_split in H2.
Qed.

End TopSort_Start_Exit.

Lemma top_sort_first_start: forall g idx (IDX: top_sort g idx) d,
  length g.(vs) > 0 ->
  is_start g (nth 0 idx d).
Proof.
  intros. apply dual_start_exit. apply dual_top_sort in IDX as IDX'.
  enough (h: nth 0 idx d = nth (length idx - 1) (rev idx) d).
  { rewrite h. replace (length idx) with (length (dual g).(vs)); [ apply top_sort_last_exit; auto |].
    rewrite <- top_sort_len with (idx := rev idx); [ apply rev_length | auto ]. }
  { replace idx with (rev (rev idx)) at 1 by apply rev_involutive.
    replace (length idx) with (length (rev idx)) by now rewrite rev_length. apply rev_nth; now rewrite rev_length, top_sort_len with (g:=g). }
Qed.

Lemma top_sort_path_from_start: forall g idx (IDX: top_sort g idx) v,
  vertex g v ->
  length g.(vs) > 0 ->
  exists s, is_start g s /\ s →* v in g.
Proof.
  intros.
  apply dual_top_sort in IDX as IDX'. apply top_sort_path_to_exit with (v:=v) in IDX' as [s []]; auto.
  exists s. now split; [ apply dual_start_exit | apply dual_path ].
Qed.

Lemma edge_start: forall g s v,
  is_start g s -> ~ v → s in g.
Proof.
  intros. intro. destruct H. apply predecessors_spec in H0; auto. now rewrite H1 in H0.
Qed.

Lemma edge_exit: forall g e v,
  is_exit g e -> ~ e → v in g.
Proof.
  intros. intro. destruct H. apply successors_spec in H0; auto. now rewrite H1 in H0.
Qed.

Lemma path_start: forall g s v,
  is_start g s -> v →* s in g -> v = s.
Proof.
  intros. induction H0. auto. copy H. apply IHpath in H. subst. exfalso. enow eapply edge_start in H2.  
Qed.

Lemma path_exit: forall g e v,
  is_exit g e -> e →* v in g -> v = e.
Proof.
  intros. induction H0. auto. exfalso. enow eapply edge_exit in H.  
Qed.

(*** MORE ***)

Lemma postdom_beforeeq: forall g exit idx (IDX: top_sort g idx) v w,
  (forall e, is_exit g e <-> e = exit) -> postdom g exit v w -> w <<= v in idx.
Proof.
  intros. copy IDX.
  apply top_sort_path_to_exit with (v:=w) in IDX as [e []];
  [| destruct H0, g.(vs) eqn:G; unfold vertex in H0; rewrite G in *; [contradiction | simpl; lia] | now destruct H0].
  apply H in H1. subst. apply postdom_split with (v:=v) in H2; auto. destruct H2. eapply path_beforeeq in H1; eauto. 
Qed.

Lemma postdom_before: forall g exit idx (IDX: top_sort g idx) v w,
  (forall e, is_exit g e <-> e = exit) -> postdom g exit v w -> v <> w -> w << v in idx.
Proof.
  intros. eapply postdom_beforeeq in H0; eauto. apply (beforeeq_split Nat.eq_dec) in H0 as []; [lia|auto].
Qed.
  
Lemma postdom_both: forall g exit idx (IDX: top_sort g idx) (ND: NoDup idx) v w,
  (forall e, is_exit g e <-> e = exit) -> postdom g exit v w -> postdom g exit w v -> v = w.
Proof.
  intros. eapply postdom_beforeeq in H0; eauto. eapply postdom_beforeeq in H1; eauto. enow eapply (beforeeq_both Nat.eq_dec).
Qed.

Lemma strong_graph_rect_dual: forall g idx (IDX: top_sort g idx) (P: V -> Type),
  (forall v, vertex g v -> (forall p, p <> v -> v →* p in g -> P p) -> P v) ->
  forall v, vertex g v -> P v.
Proof.
  intros.
  apply strong_graph_rect with (g:=dual g) (idx:=rev idx).
  * apply dual_top_sort. now rewrite dual_dual, rev_involutive.
  * intros. apply X; auto. intros. apply X0; auto. now apply dual_path in H2.
  * now apply dual_vertex in H.
Qed.

Lemma strong_graph_ind_dual: forall g idx (IDX: top_sort g idx) (P: V -> Prop),
  (forall v, vertex g v -> (forall p, p <> v -> v →* p in g -> P p) -> P v) ->
  forall v, vertex g v -> P v.
Proof.
  intros. enow eapply strong_graph_rect_dual.
Qed.

Lemma graph_rect_dual: forall g idx (IDX: top_sort g idx) (P: V -> Type),
  (forall v, vertex g v -> (forall p, v → p in g -> P p) -> P v) ->
  forall v, vertex g v -> P v.
Proof.
  intros. eapply strong_graph_rect_dual; eauto.
  intros. apply X; auto. intros. apply X0; auto. intro. enow eapply edge_neq.
Qed.

Lemma graph_ind_dual: forall g idx (IDX: top_sort g idx) (P: V -> Prop),
  (forall v, vertex g v -> (forall p, v → p in g -> P p) -> P v) ->
  forall v, vertex g v -> P v.
Proof.
  intros. enow eapply graph_rect_dual.
Qed.