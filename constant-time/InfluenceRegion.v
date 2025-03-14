Require Import Axioms Coqlib Datatypes List.
Require Import Common ListsExtra Before Graph GraphDual.
Require Import Coq.Program.Equality.

Section IR.

Variable g: G.
Variable exit: V.
Hypothesis EXIT: forall v, v = exit <-> is_exit g v.
Variable idx: list V.
Hypothesis IDX: top_sort g idx.

Lemma NN: length g.(vs) > 0.
Proof.
  assert (In exit g.(vs)) by now apply EXIT. destruct g.(vs). easy. simpl. lia.
Qed.

Lemma exit_vertex: vertex g exit.
Proof.
  now apply EXIT.
Qed.

Notation "v ▷ w" := (postdom g exit w v) (at level 49).


(*** SOME DECIDABILITY AND POSTDOM STUFF ***)

Lemma path_dec: forall v w, {v →* w in g} + {~ v →* w in g}.
Proof.
  intros. destruct (vertex_dec g v), (vertex_dec g w).
  - case (Nat.eq_dec v w); intro. left. enow subst.
    pose (P v := {v →* w in g} + {~ v →* w in g}).
    apply graph_rect_dual with (g:=g) (idx:=idx) (v:=v) (P:=P); auto.
    intros. unfold P in *.
    (* Filter successors by those that admit a path to w *)
    pose (s := successors g v2).
    epose (s' := map_extra_id s (fun a => v2 → a in g) ltac:(intro; enow eapply successors_spec)). eassert (s' = map_extra_id _ _ _) by easy.
    destruct s'.
    epose (x' := filter _ x). Unshelve. 2: { intros []. apply H0 in e0. exact (proj_sumbool e0). }
    (* Are there any such successors? *)
    case x' eqn:?.
    * case (Nat.eq_dec v2 w) eqn:?.
      + left. enow subst.
      + right. intro. inv H2. lia.
        eenough (I: In (exist _ v3 ?[X]) x') by now rewrite Heql in I.
        apply filter_In. assert (In v3 s) by now apply successors_spec.
        eapply map_extra_id_In_rev in H2; [|apply Nat.eq_dec]. rewrite <- H1 in H2. destruct H2. destruct x0. simpl in H2. destruct H2.
        split. subst. irrel ?X e0. apply H2. now destruct H0.
    * left. destruct s0. constructor 2 with (v:=x0); auto.
      assert (In [x0] x') by (rewrite Heql; apply in_eq). apply filter_In in H2 as [].
      now destruct H0 in H3.
  - right. intro. now apply path_vertex_right in H.
  - right. intro. enow destruct H.
  - right. intro. enow destruct H.
  Unshelve. auto.
Qed.

Lemma postdom_dec: forall v w, {v ▷ w} + {~ v ▷ w}.
Proof.
  intros. destruct (vertex_dec g v), (vertex_dec g w).
  - case (Nat.eq_dec v w); intro. left. subst. apply postdom_refl; auto. apply exit_vertex.
    case (Nat.eq_dec v exit); intro. { right. intro. subst. enow apply postdom_exit_2 in H. }
    pose (P v := {v ▷ w} + {~ v ▷ w}).
    apply graph_rect_dual with (g:=g) (idx:=idx) (v:=v) (P:=P); auto.
    intros. unfold P in *.
    case (Nat.eq_dec v2 exit) eqn:?, (Nat.eq_dec w exit) eqn:?.
    + left. subst. apply postdom_exit_1; auto.
    + right. subst. intro. now apply postdom_exit_2 in H1.
    + left. subst. apply postdom_exit_1; auto.
    + case (Nat.eq_dec v2 w) eqn:?. left. subst. apply postdom_refl; auto; apply exit_vertex.
      (* Filter successors by those that admit a path to w *)
      pose (s := successors g v2).
      epose (s' := map_extra_id s (fun a => v2 → a in g) ltac:(intro; enow eapply successors_spec)). eassert (s' = map_extra_id _ _ _) by easy.
      destruct s'.
      epose (x' := filter _ x). Unshelve. 2: { intros []. apply H0 in e0. exact (proj_sumbool e0). }
      (* Do *all* successors admit such a path? *)
      case (Nat.eq_dec (length x') (length x)); intro.
      * left. apply filter_length_eq in e0. apply postdom_spec; auto. apply exit_vertex. right. split; auto.
        intros. assert (In w' s) by now apply successors_spec. eapply map_extra_id_In_rev in H3; [|apply Nat.eq_dec].
        destruct H3, H3, x0. rewrite <- H1 in H3. simpl in *. rewrite <- e0 in H3.
        apply filter_In in H3 as []. destruct H0 in H5. now subst. easy.
      * right. apply filter_length_neq in n4 as [? []]. simpl in H3. destruct x0, H0 in H3. easy.
        intro. apply postdom_spec in H4; auto; [|apply exit_vertex]. destruct H4 as [|[]]; [lia|].
        now apply n4, H5.
  - right. intro. unfold postdom in H. easy.
  - right. intro. unfold postdom in H. easy.
  - right. intro. unfold postdom in H. easy.
Qed.

Lemma postdom_linear: forall v w1 w2,
  v ▷ w1 -> v ▷ w2 ->
  w1 ▷ w2 \/ w2 ▷ w1.
Proof.
  pose (P v := forall w1 w2, v ▷ w1 -> v ▷ w2 -> w1 ▷ w2 \/ w2 ▷ w1).
  intros.
  exploit graph_ind_dual. Unshelve. 7: exact P. 1: apply IDX.
  unfold P in *. intros.
  case (Nat.eq_dec v0 exit) eqn:?.
  * assert (w0 = exit) by (subst; enow eapply postdom_exit_2). assert (w3 = exit) by (subst; enow eapply postdom_exit_2).
    subst. left. apply postdom_refl; apply exit_vertex.
  * case (successors g v0) eqn:?.
  + assert (is_exit g v0). split; auto. now apply EXIT in H5.
  + case (Nat.eq_dec v0 w0) eqn:?. left. now subst. case (Nat.eq_dec v0 w3) eqn:?. right. now subst.
    assert (vertex g w0) by now destruct H3. assert (vertex g w3) by now destruct H4. assert (vertex g exit) by apply exit_vertex.
    apply postdom_spec in H3 as [| []]; auto. lia. apply postdom_spec in H4 as [| []]; auto. lia.
    assert (v0 → v1 in g) by (apply successors_spec; auto; rewrite Heql; apply in_eq). copy H10. copy H10.
    apply H8 in H10. apply H9 in H11. enow eapply H2 in H12.
  * destruct H. destruct a. exact v1.
  * auto. 
Qed.

Lemma postdom_linear_dec: forall v w1 w2,
  v ▷ w1 -> v ▷ w2 ->
  {w1 ▷ w2} + {w2 ▷ w1}.
Proof.
  intros. eapply postdom_linear in H; eauto.
  pose proof (postdom_dec w1 w2). pose proof (postdom_dec w2 w1).
  case H1, H2; intros.
  * now left. * now left. * now right. * exfalso. now case H.
Qed.


(*** IMMEDIATE POSTDOMINATOR ***)

Definition is_ipd (ipd v: V) :=
  v ▷ ipd /\ v <> ipd /\ forall pd, v ▷ pd -> v <> pd -> ipd →* pd in g.

Definition ipd_unique: forall i1 i2 v,
  is_ipd i1 v -> is_ipd i2 v -> i1 = i2.
Proof.
  unfold is_ipd. intros. decompose [and] H. decompose [and] H0.
  apply H4 in H2; auto. apply H7 in H1; auto. eapply path_beforeeq in H2; eauto. eapply path_beforeeq in H1; eauto.
  eapply (beforeeq_both Nat.eq_dec); eauto. enow eapply top_sort_nodup.
Qed.

Definition all_pds (v: V) := filter (fun pd => postdom_dec v pd && negb (pd =? v)) g.(vs).

Lemma all_pds_spec: forall v pd, vertex g v ->
  (In pd (all_pds v) <-> (v ▷ pd /\ v <> pd)).
Proof.
  intros. unfold all_pds. split; intro.
  * apply filter_In in H0 as []. apply andb_prop in H1 as []. apply negb_true_iff, Nat.eqb_neq in H2. enow destruct postdom_dec.
  * apply filter_In. split. destruct H0, H0. auto. apply andb_true_iff. split. now destruct postdom_dec. apply negb_true_iff, Nat.eqb_neq. lia.
Qed.

Lemma all_pds_vertex: forall v pd, vertex g v -> v <> exit -> In pd (all_pds v) -> vertex g pd.
Proof.
  intros. copy H. eapply all_pds_spec in H; eauto. apply H in H1. now destruct H, H1, H1.
Qed.

Lemma all_pds_min:
  forall v pds,
  vertex g v -> v <> exit ->
  pds <> nil ->
  incl pds (all_pds v) ->
  { i: V | In i pds /\ forall x, In x pds -> i ▷ x }.
Proof.
  intros. induction pds in *.
  * congruence.
  * case pds in *.
  + apply incl_cons_inv in H2 as []. exists a. split; [apply in_eq|].
    intros. destruct H4; [|easy]. subst. apply postdom_refl. apply exit_vertex. enow eapply all_pds_vertex.
  + assert (v0 :: pds <> nil) by easy. apply IHpds in H3 as []; [|enow eapply incl_cons_inv].
    assert (v ▷ x). { destruct a0. apply all_pds_spec; auto. now apply H2, in_cons. }
    assert (v ▷ a). { destruct a0. apply all_pds_spec; auto. now apply H2, in_eq. }
    destruct a0. eapply postdom_linear_dec in H3 as []; eauto.
    - exists a. split. apply in_eq.
      intros. destruct H3.
      subst; apply postdom_refl. apply exit_vertex. now destruct p.
      apply H6 in H3. enow eapply postdom_concat.
    - exists x. split. apply in_cons, H5.
      intros. destruct H3. now subst. now apply H6 in H3.
Qed.

Definition ipd': forall v,
  vertex g v ->
  v <> exit ->
  { i: V | is_ipd i v }.
Proof.
  intros. eapply all_pds_min in H0; eauto. 3: apply incl_refl.
  * destruct H0. destruct a. exists x. apply all_pds_spec in H0 as []; auto.
    split; auto. split; auto. intros.
    eapply postdom_path; eauto. apply NN.
    now apply H1, all_pds_spec.
  * enough (In exit (all_pds v)) by (intro; rewrite H2 in H1; easy).
    apply filter_In. split. apply exit_vertex. apply andb_true_iff. split.
    eapply postdom_exit_1 with (exit:=exit) in H; eauto; [|apply exit_vertex]. now destruct postdom_dec.
    enow apply negb_true_iff, Nat.eqb_neq.
Qed.

Definition ipd v := match (vertex_dec g v), (Nat.eq_dec v exit) with
  | left _, right _ => !(ipd' v ltac:(auto) ltac:(auto))
  | _, _ => 0
  end.

Lemma ipd_same: forall v x y,
  vertex g v -> v <> exit -> !(ipd' v x y) = ipd v.
Proof.
  unfold ipd. intros. case vertex_dec; [|congruence]. case Nat.eq_dec; [congruence|].
  intros. do 2 destruct ipd'. simpl. enow eapply ipd_unique.
Qed.

Lemma ipd_is_ipd: forall c,
  vertex g c -> c <> exit -> is_ipd (ipd c) c.
Proof.
  intros. erewrite <- ipd_same; auto. destruct ipd'. now simpl.
  Unshelve. auto. auto.
Qed.

Lemma ipd_vertex: forall c,
  vertex g c -> c <> exit -> vertex g (ipd c).
Proof.
  intros. pose proof (ipd_is_ipd c H H0). now destruct H1, H1.
Qed.

Lemma ipd_different: forall c,
  vertex g c -> c <> exit -> c <> ipd c.
Proof.
  intros. pose proof (ipd_is_ipd c H H0). now destruct H1, H2.
Qed.

(*** INFLUENCE REGION ***)

Definition in_ir (c v: V): Prop :=
  match (vertex_dec g c), (Nat.eq_dec c exit) with
  | left _, right _ => let ipd := ipd' c ltac:(auto) ltac:(auto) in c →* v in g /\ c <> v /\ v ▷ (!ipd)
  | _, _ => False
  end.

Notation "x ∈ 'ir' ( c )" := (in_ir c x) (at level 50).

Definition in_ir_spec: forall c x,
  c <> exit ->
  x ∈ ir(c) <-> (c →* x in g /\ x <> c /\ x ▷ ipd c).
Proof.
  intros. unfold in_ir. case vertex_dec eqn:?. case Nat.eq_dec eqn:?.
  * split. easy. intros. lia.
  * split; intros [? []].
    + split; auto. split; auto. now rewrite ipd_same in H2.
    + split; auto. split; auto. now rewrite ipd_same.
  * split. easy. intros []. enow destruct H0.
Qed.

Definition in_ir_dec c v : {v ∈ ir(c)} + {~ v ∈ ir(c)}.
Proof.
  unfold in_ir.
  case vertex_dec eqn:?; [ case Nat.eq_dec eqn:? |]; auto.
  case (Nat.eq_dec c v) eqn:?; [ now right |].
  case (path_dec c v) eqn:?; [| now right ].
  case (postdom_dec v (!(ipd' c v0 n))) eqn:?; [| now right ].
  now left.
Defined.

Definition in_ir_inner_dec c v : {v ∈ ir(c) /\ v <> ipd c} + {~ (v ∈ ir(c) /\ v <> ipd c)}.
Proof.
  intros. destruct (in_ir_dec c v); [| now right ].
  destruct (Nat.eq_dec v (ipd c)). now right. now left.
Defined.

Lemma in_ir_vertex: forall c x,
  x ∈ ir(c) ->
  vertex g c /\ c <> exit /\ vertex g x.
Proof.
  intros. unfold in_ir in H. case vertex_dec in H; [|easy]. case Nat.eq_dec in H. easy. destruct H, H. auto. destruct H0. split; auto. split; auto. enow eapply path_vertex_right.
Qed.

Lemma ir_pd: forall c x,
  x ∈ ir(c) ->
  x ▷ ipd(c).
Proof.
  intros. apply in_ir_spec in H. easy. now apply in_ir_vertex in H.
Qed.

Lemma ir_pd_head: forall c,
  vertex g c ->
  c <> exit ->
  c ▷ ipd(c).
Proof.
  intros. now pose proof (ipd_is_ipd c H H0) as [].
Qed.

Lemma ir_before: forall c x,
  x ∈ ir(c) ->
  x <<= ipd(c) in idx.
Proof.
  intros. apply ir_pd in H. eapply postdom_beforeeq; eauto. intro. split; apply EXIT.
Qed.

Lemma ipd_in_ir: forall c,
  vertex g c ->
  c <> exit ->
  ipd(c) ∈ ir(c).
Proof.
  intros. apply in_ir_spec. auto. pose proof (ipd_is_ipd c H H0) as [? []].
  split. eapply postdom_path; eauto. apply NN. split; auto. apply postdom_refl; auto. now apply EXIT. now apply ipd_vertex.
Qed.

Lemma ir_exit_ipd: forall c,
  exit ∈ ir(c) ->
  exit = ipd c.
Proof.
  intros. apply ir_pd in H. now apply postdom_exit_2 in H.
Qed.

Lemma ir_edge: forall c v w,
  v ∈ ir(c) ->
  v <> ipd c ->
  v → w in g ->
  w ∈ ir(c).
Proof.
  intros. copy H. apply in_ir_vertex in H2. apply in_ir_spec in H. 2: easy.
  apply in_ir_spec. easy. destruct H, H3. split; [|split].
  * auto.
  * intro. subst. enow eapply edge_path_exclusive.
  * apply postdom_spec in H4; auto. destruct H4. lia.
    destruct H4. apply H5; auto. now apply EXIT. now apply ipd_vertex.
Qed.

Lemma ir_path: forall c v w,
  v ∈ ir(c) ->
  v →* w in g ->
  w →* ipd(c) in g ->
  w ∈ ir(c).
Proof.
  intros. induction H0.
  * auto.
  * apply IHpath; auto. eapply ir_edge in H; eauto.
    intro. subst. eapply path_concat with (u:=v) in H1; eauto. enow eapply edge_path_exclusive.
Qed.

Lemma ir_edge_head: forall c v,
  c → v in g ->
  v ∈ ir(c).
Proof.
  intros.
  assert (c <> exit). { intro. apply EXIT in H0 as []. apply successors_spec in H; auto. now rewrite H1 in H. }
  apply in_ir_spec. auto. split; auto. split.
  intro. enow eapply edge_neq.
  copy H0. apply ir_pd_head in H0; auto. apply postdom_spec in H0; auto.
  destruct H0. apply ipd_different in H1; auto. lia. destruct H0. apply H2; auto.
  now apply EXIT. enow apply ipd_vertex.
Qed.

Lemma ir_path_head: forall c v,
  c →* v in g ->
  c <> v ->
  v →* ipd(c) in g ->
  v ∈ ir(c).
Proof.
  intros. destruct H. lia. apply ir_edge_head in H. enow eapply ir_path.
Qed.

Lemma ir_before_not_ipd: forall c v w,
  v ∈ ir(c) ->
  w ∈ ir(c) ->
  v << w in idx ->
  v <> ipd(c).
Proof.
  intros. intro. subst. eapply ir_pd, postdom_beforeeq in H0; eauto. apply (beforeeq_unique Nat.eq_dec) in H1; auto. enow eapply top_sort_nodup.
  intros. split; intro; now apply EXIT.
Qed.

Lemma ir_predecessor: forall c v,
  v ∈ ir(c) ->
  exists w, (w ∈ ir(c) \/ w = c) /\ w <> ipd c /\ w → v in g.
Proof.
  intros. copy H. apply in_ir_spec in H as [? []]. 2: now apply in_ir_vertex in H0.
  apply path_right_inv in H as [w []]; auto.
  case (Nat.eq_dec c w) eqn:?.
  * subst. exists w. split; auto. split; auto. apply ipd_different; auto.
    intro. apply edge_exit in H3. auto. now apply EXIT.
  * apply ir_path_head in H; auto.
    - exists w. split; auto. split; auto.
      intro. subst. eapply edge_before in H3; eauto. eapply postdom_path in H2; eauto. 2: apply NN.
      eapply path_beforeeq in H2; eauto. apply (beforeeq_swap Nat.eq_dec) in H2; auto. eapply top_sort_nodup, IDX.
    - eapply postdom_path in H2; eauto. apply NN.
Qed.

Lemma pd_outside_ir: forall c v,
  c ▷ v ->
  c <> v ->
  ~ (v ∈ ir(c) /\ v <> ipd c).
Proof.
  intros. intros []. assert (vertex g c) by now destruct H. assert (c <> exit) by now apply in_ir_vertex in H1.
  apply ipd_is_ipd in H3; auto. destruct H3, H5. apply H6 in H; auto.
  apply in_ir_spec in H1; auto. destruct H1, H7. eapply postdom_path in H8; eauto. 2: apply NN.
  apply H2. eapply (beforeeq_both Nat.eq_dec). enow eapply top_sort_nodup.
  enow eapply path_beforeeq. enow eapply path_beforeeq.
Qed.

(*** DIRECT INTERSECTION ***)

Definition intersect c1 c2 := exists t, t ∈ ir(c1) /\ t ∈ ir(c2).

Notation "c1 ∩ c2" := (intersect c1 c2) (at level 50).

Lemma intersect_vertex: forall c1 c2,
  c1 ∩ c2 -> vertex g c1 /\ vertex g c2 /\ c1 <> exit /\ c2 <> exit.
Proof.
  intros. destruct H as [? []]. now apply in_ir_vertex in H, H0.
Qed.

Lemma intersect_refl: forall c,
  vertex g c -> c <> exit -> c ∩ c.
Proof.
  intros. exists (ipd c). split; now apply ipd_in_ir.
Qed.

Lemma intersect_sym: forall c1 c2,
  c1 ∩ c2 -> c2 ∩ c1.
Proof.
  intros. destruct H. now exists x.
Qed.

Notation "c1 ≼ c2" := (ipd(c1) ∈ ir(c2) /\ vertex g c1 /\ c1 <> exit) (at level 50). (* \preceq *)
Notation "c1 ≄ c2" := (ipd(c1) <> ipd(c2)) (at level 50).
Notation "c1 ≺ c2" := (c1 ≼ c2 /\ c1 ≄ c2) (at level 50).

Lemma smaller_vertex: forall c1 c2,
  c1 ≼ c2 -> vertex g c1 /\ vertex g c2 /\ c1 <> exit /\ c2 <> exit.
Proof.
  intros. destruct H, H0. apply in_ir_vertex in H. easy.
Qed.

Lemma smaller_refl: forall c,
  vertex g c ->
  c <> exit ->
  c ≼ c.
Proof.
  intros. repeat split; auto. now apply ipd_in_ir.
Qed.

Lemma smaller_intersect: forall c1 c2,
  c1 ≼ c2 -> c1 ∩ c2.
Proof.
  intros. exists (ipd c1). split. apply smaller_vertex in H. now apply smaller_refl. easy.
Qed.

Lemma smaller_before: forall c1 c2,
  c1 ≼ c2 -> ipd c1 <<= ipd c2 in idx.
Proof.
  intros.
  assert (ipd c1 ▷ ipd c2) by now apply ir_pd.
  eapply postdom_beforeeq; eauto. intros. split; apply EXIT.
Qed.

Lemma merge_three_intersecting: forall c1 c2 c3,
  c2 ≼ c1 -> c2 ≼ c3 -> c1 ∩ c3.
Proof.
  intros. now exists (ipd c2).
Qed.

Theorem intersect_option: forall c1 c2,
  c1 ∩ c2 ->
  c1 ≺ c2 \/ c2 ≼ c1.
Proof.
  intros. destruct H as [t []]. pose NN.
  copy H. copy H0. apply in_ir_vertex in H, H0.
  case (Nat.eq_dec (ipd c1) (ipd c2)) eqn:?.
  * right. repeat split; try easy. rewrite <- e. now apply ipd_in_ir.
  * copy H1. copy H2. apply ir_pd in H1, H2. copy H1. copy H2. eapply postdom_path in H1, H2; eauto.
    eapply postdom_linear in H5 as []; eauto.
    + right. eapply postdom_path in H5; eauto. repeat split; try easy. enow eapply ir_path.
    + left. eapply postdom_path in H5; eauto. repeat split; try easy. enow eapply ir_path.
Qed.


(*** CHAINED INTERSECTION ***)

Reserved Notation "c1 ∩( cs )∩ c2" (at level 50).

Inductive chain_via: list V -> V -> V -> Prop :=
  | chain_base: forall c1 c2,
                c1 ∩ c2 -> c1 ∩(nil)∩ c2
  | chain_more: forall c1 c2 c3 cs,
                c1 ∩ c2 -> c2 ∩(cs)∩ c3 -> c1 ∩(c2::cs)∩ c3
where "c1 ∩( cs )∩ c2" := (chain_via cs c1 c2).

Notation "c1 ∩...∩ c2" := (exists cs, c1 ∩(cs)∩ c2) (at level 50).

Lemma weaken_chain: forall c1 c2 cs,
  c1 ∩(cs)∩ c2 -> c1 ∩...∩ c2.
Proof.
  intros. now exists cs.
Qed.

Lemma chain_from_intersection: forall c1 c2,
  c1 ∩ c2 -> c1 ∩...∩ c2.
Proof.
  intros. eapply weaken_chain. now constructor.
Qed.

Lemma chain_vertex: forall c1 c2,
  c1 ∩...∩ c2 -> vertex g c1 /\ vertex g c2 /\ c1 <> exit /\ c2 <> exit.
Proof.
  intros. destruct H. induction H; now apply intersect_vertex in H.
Qed.

Lemma chain_right: forall c1 c2 c3 cs,
  c1 ∩(cs)∩ c2 -> c2 ∩ c3 -> c1 ∩(cs++c2::nil)∩ c3.
Proof.
  intros. induction H.
  * constructor. auto. now constructor.
  * apply IHchain_via in H0. now constructor.
Qed.

Lemma chain_refl_full: forall c,
  vertex g c -> c <> exit -> c ∩(nil)∩ c.
Proof.
  intros. constructor. now apply intersect_refl.
Qed.

Lemma chain_refl: forall c,
  vertex g c -> c <> exit -> c ∩...∩ c.
Proof.
  intros. exists nil. constructor. now apply intersect_refl.
Qed.

Lemma chain_sym_full: forall c1 c2 cs,
  c1 ∩(cs)∩ c2 -> c2 ∩(rev cs)∩ c1.
Proof.
  intros. induction H. simpl. constructor. now apply intersect_sym.
  simpl. apply chain_right. auto. now apply intersect_sym.
Qed.

Lemma chain_sym: forall c1 c2,
  c1 ∩...∩ c2 -> c2 ∩...∩ c1.
Proof.
  intros. destruct H. apply chain_sym_full in H. now exists (rev x).
Qed.

Lemma chain_trans_full: forall c1 c2 c3 cs cs',
  c1 ∩(cs)∩ c2 -> c2 ∩(cs')∩ c3 -> c1 ∩(cs++c2::cs')∩ c3.
Proof.
  intros. induction H.
  * simpl. now constructor.
  * simpl. apply IHchain_via in H0. now constructor.
Qed.

Lemma chain_trans: forall c1 c2 c3,
  c1 ∩...∩ c2 -> c2 ∩...∩ c3 -> c1 ∩...∩ c3.
Proof.
  intros. destruct H, H0. enow eapply chain_trans_full in H0.
Qed.

(* Jesus breaks all chains *)
Lemma break_chain: forall c1 c2 cs c,
  c1 ∩(cs)∩ c2 ->
  In c (c1::c2::cs) ->
  exists cs' cs'',
    incl cs' cs /\ incl cs'' cs /\ c1 ∩(cs')∩ c /\ c ∩(cs'')∩ c2.
Proof.
  intros. copy H. apply weaken_chain, chain_vertex in H1.
  induction H.
  * destruct H0.
    + subst. exists nil, nil. repeat split; try easy. now apply chain_refl_full. now constructor.
    + destruct H0; try easy. subst. exists nil, nil. repeat split; try easy. now constructor. now apply chain_refl_full.
  * destruct H0.
    + subst. exists nil, (c2::cs). repeat split; try easy. now apply chain_refl_full. enow econstructor.
    + assert (In c (c2::c3::cs)) by (simpl; enow repeat destruct H0).
      apply IHchain_via in H3. 2: now apply intersect_vertex in H.
      destruct H3, H3. exists (c2::x), x0. repeat split; try easy. now apply incl_same_head. now apply incl_tl. now constructor.
Qed.

Lemma chain_break_first: forall c1 c2 c3 cs,
  c1 ∩(c2::cs)∩ c3 -> c2 ∩(cs)∩ c3.
Proof.
  intros. dependent induction H. now subst.
Qed.


(*** MAIN THEOREM ***)

Notation "c1 ≽ c2" := (c2 ≼ c1) (at level 50). (* \succeq *) 

Reserved Notation "c1 ≽( cs )≽ c2" (at level 50).

Inductive greater_chain: V -> list V -> V -> Prop :=
  | greater_base: forall c1 c2,
                  c1 ≽ c2 -> c1 ≽(nil)≽ c2
  | greater_more: forall c1 cs c2 c3,
                  c1 ≽ c2 -> c2 ≽(cs)≽ c3 -> c1 ≽(c2::cs)≽ c3
where "c1 ≽( cs )≽ c2" := (greater_chain c1 cs c2).

Lemma greater_chain_before: forall c1 cs c2,
  c1 ≽(cs)≽ c2 -> ipd c2 <<= ipd c1 in idx.
Proof.
  intros. induction H; apply smaller_before in H. auto.
  eapply beforeeq_trans in H; eauto. enow eapply top_sort_nodup.
Qed.

Lemma chain_containment_helper: forall c1 ck cs,
  c1 ∩(cs)∩ ck ->
  c1 ≽(cs)≽ ck \/ c1 ≺ hd ck cs \/ exists cs', incl cs' cs /\ length cs' < length cs /\ c1 ∩(cs')∩ ck.
Proof.
  intros. induction H.
  * apply intersect_option in H as []; [ right; now left | left; now constructor ].
  * apply intersect_option in H as []; [ right; now left | ].
    decompose [or] IHchain_via.
    + left. now constructor.
    + simpl in *. apply merge_three_intersecting with (c3:=hd c3 cs) in H; [|now destruct H2].
      right. right. exists cs. repeat split.
      - now apply incl_tl, incl_refl.
      - lia.
      - case cs in *; simpl in *. now constructor. constructor. auto. now apply chain_break_first in H0.
    + decompose [ex and] H2. right. right. exists (c2::x). repeat split.
      - now apply incl_same_head.
      - simpl. lia.
      - apply smaller_intersect, intersect_sym in H. now constructor.
Qed.

(* Main theorem for proving that the chain-invariant holds. *)
Theorem chain_containment: forall c1 c2 cs,
  c1 ∩(cs)∩ c2 ->
  ipd(c1) << ipd(c2) in idx ->
  exists c, In c (c1::c2::cs) /\ c1 ≺ c.
Proof.
  intros. induction cs using list_length_ind.
  apply chain_containment_helper in H as [|[|]].
  * apply greater_chain_before in H. exfalso. eapply (beforeeq_swap Nat.eq_dec) in H; eauto. enow eapply top_sort_nodup.
  * exists (hd c2 cs). split; auto. enow case cs; simpl.
  * decompose [ex and] H. apply H1 in H5 as [? []]; auto.
    exists x0. split; auto. repeat destruct H4. now subst. subst; now apply in_cons, in_eq.
    repeat apply in_cons. now apply H3.
Qed.


(*** CHAIN-INVARIANT USED BY PCFL AND TAINT ANA ***)

Definition chain_inv (u: V -> bool) v w :=
  exists cv cw cs, (forall c, In c (cv::cw::cs) -> u c = false) /\ v ∈ ir(cv) /\ w ∈ ir(cw) /\ cv ∩(cs)∩ cw.

Lemma chain_inv_sym: forall u v w,
  chain_inv u v w -> chain_inv u w v.
Proof.
  intros. unfold chain_inv in *. decompose [ex and] H.
  exists x0, x, (rev x1). repeat split; auto.
  + intros. repeat destruct H3. apply H1, in_cons, in_eq. apply H1, in_eq. now apply H1, in_cons, in_cons, in_rev.
  + now apply chain_sym_full.
Qed.

Lemma chain_inv_direct_edge: forall u v w v_targ,
  v → w in g ->
  v << v_targ in idx ->
  chain_inv u v v_targ ->
  chain_inv u w v_targ.
Proof.
  intros.
  assert (ND: NoDup idx) by enow eapply top_sort_nodup.
  unfold chain_inv in *. decompose [ex and] H1.
  case (Nat.eq_dec v (ipd x)) eqn:?.
  * subst v.
    assert (ipd x << ipd x0 in idx). { apply beforeeq_trans_2 with (y:=v_targ); auto. now apply ir_before. }
    copy H6. apply chain_containment in H6; auto. decompose [ex and] H6.
    apply break_chain with (c:=x2) in H7; auto. decompose [ex and] H7.
    exists x2, x0, x4. repeat split; auto.
    + intros. repeat destruct H16. apply H3, H9. apply H3, in_cons, in_eq. apply H3, in_cons, in_cons, H14, H16.
    + now apply ir_edge with (v:=ipd x).
  * exists x, x0, x1. repeat split; auto. now apply ir_edge with (v:=v).
Qed.

Lemma chain_inv_indirect_edge: forall u v x w v_targ,
  v → x in g ->
  v << v_targ in idx ->
  chain_inv u x w ->
  chain_inv u v v_targ ->
  chain_inv u w v_targ.
Proof.
  intros.
  assert (ND: NoDup idx) by enow eapply top_sort_nodup.
  unfold chain_inv in *. decompose [ex and] H1. decompose [ex and] H2.
  case (Nat.eq_dec v (ipd x3)) eqn:?.
  * subst v.
    assert (ipd x3 << ipd x4 in idx). { apply beforeeq_trans_2 with (y:=v_targ); auto. now apply ir_before. }
    copy H11. apply chain_containment in H11; auto. decompose [ex and] H11.
    apply break_chain with (c:=x6) in H12; auto. decompose [ex and] H12.
    exists x1, x4, (rev x2 ++ x0 :: x6 :: x8). repeat split; auto.
    + intros. repeat destruct H21. apply H4, in_cons, in_eq. apply H8, in_cons, in_eq.
      apply in_app in H21 as []. apply H4, in_cons, in_cons, in_rev, H21.
      repeat destruct H21. apply H4, in_eq. apply H8, H14. apply H8, in_cons, in_cons, H19, H21.
    + apply chain_trans_full. now apply chain_sym_full. constructor; auto.
      exists x. split; auto. enow eapply ir_edge.
  * exists x1, x4, (rev x2 ++ x0 :: x3 :: x5). repeat split; auto.
    + intros. repeat destruct H10. apply H4, in_cons, in_eq. apply H8, in_cons, in_eq.
      apply in_app in H10 as []. apply H4, in_cons, in_cons, in_rev, H10.
      repeat destruct H10. apply H4, in_eq. apply H8, in_eq. apply H8, in_cons, in_cons, H10.
    + apply chain_trans_full. now apply chain_sym_full. constructor; auto.
      exists x. split; auto. enow eapply ir_edge.
Qed.

End IR.
