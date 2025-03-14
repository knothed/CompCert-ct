Require Import Axioms Common Coqlib Classical Datatypes.
Require Import AST Memory Registers Maps Values Events Globalenvs Smallstep Op Integers.
Require Import GraphRTL ListsExtra Before.
Require Import Graph GraphDual.
Require Import Smallstep Errors.
Require Import Permutation.
Require Import PCFL.

Section AlgoFacts.

Variable f: function.
Let idx := f.(idx).
Let IDX := f.(IDX).
Let n := f.(n).

Variable u: V -> bool.

Notation "[[ e ]]" := (existT _ e _) (at level 10).
Notation "& x" := (projT1 x) (at level 10).
Notation "? x" := (projT2 x) (at level 10).

Definition step_data_inv := step_data_inv f u.

Definition step := step_inv_step f u.
Notation "@ i" := (pow step i (step_empty f u)) (at level 30).

Definition step_invariant := step_invariant f u.

Let pcfl := el_graph f u (@n).

Lemma result_vertex_iff: forall v, vertex pcfl v <-> vertex f.(g) v.
Proof.
  unfold pcfl, el_graph, vertex, vs. firstorder.
Qed.
Hint Extern 1 => apply result_vertex_iff : core.

Ltac unfold_step_1 h := unfold step, step_inv_step, pcfl_step; simpl; case (Nat.eq_dec h.(i) f.(GraphRTL.n)) eqn:E1; simpl; auto; try lia.
Ltac unfold_step_2 h := case (Nat.eq_dec h.(i) (f.(GraphRTL.n)-1)) eqn:E2; simpl; auto; try lia. 
Ltac unfold_step h := unfold_step_1 h; try unfold_step_2 h.

Ltac unfold_step_in_1 H h := unfold step, step_inv_step, pcfl_step in H; simpl in H; case (Nat.eq_dec h.(i) f.(GraphRTL.n)) eqn:E1 in H; simpl; simpl in H; auto; try lia.
Ltac unfold_step_in_2 H h := case (Nat.eq_dec h.(i) (f.(GraphRTL.n)-1)) eqn:E2 in H; simpl; simpl in H; auto; try lia. 
Ltac unfold_step_in H h := unfold_step_in_1 H h; try unfold_step_in_2 H h.


Lemma pow_bracket: forall A n f (x: A), f (pow f n x) = pow f n (f x).
Proof.
  induction n0; intros; [now simpl | simpl; now rewrite IHn0].
Qed.

Lemma pow_succ: forall A n f (x: A), f (pow f n x) = pow f (S n) x.
Proof.
  induction n0; now intros; now rewrite pow_bracket.
Qed.

Lemma pow_i: forall j, j <= n -> (&@j).(i) = j.
Proof.
  induction j; auto.
  intro. assert (j <= n) by lia. apply IHj in H0. rewrite <- pow_succ. remember (@j). unfold_step (&s). case u; simpl; lia. 
Qed.

Lemma b_of_index: forall iv v,
  Some v = nth_error idx iv ->
  b f (&@iv) = v.
Proof.
  intros. unfold b. rewrite pow_i. now apply nth_error_nth.
  symmetry in H. apply nth_error_len in H. unfold idx in H. rewrite idx_len in H. lia.
Qed.


(*** Proof irrelevance lemmata ***)

Lemma step_invariant_proof_irr: forall (hm: step_data) (inv1: step_invariant hm) (inv2: step_invariant hm), inv1 = inv2.
Proof.
  intros. destruct inv1, inv2.
  generalize DP DP0 EP EP0 PF PF0. clear DP DP0 EP EP0.
  replace P0 with P by now subst. clear PF0 PF. intros.
  irrel PF0 PF. irrel DP0 DP. irrel EP0 EP. irrel I0 I. irrel EI0 EI. irrel DI0 DI. irrel DV0 DV. irrel DT0 DT. now irrel EV0 EV.
Qed.

Lemma calcT_proof_irr: forall hm1 hm2 a1 a2 b1 b2,
  hm1 = hm2 ->
  !(calcT f u hm1 a1 b1) = !(calcT f u hm2 a2 b2).
Proof.
  intros. generalize a1 a2 b1 b2. clear a1 a2 b1 b2.
  replace hm1 with hm2. intros. replace a1 with a2 by apply step_invariant_proof_irr. now irrel b1 b2.
Qed.

Lemma calcS_proof_irr: forall hm1 hm2 a1 a2 b1 b2,
  hm1 = hm2 ->
  !(calcS f u hm1 a1 b1) = !(calcS f u hm2 a2 b2).
Proof.
  intros. generalize a1 a2 b1 b2. clear a1 a2 b1 b2.
  replace hm1 with hm2. intros. replace a1 with a2 by apply step_invariant_proof_irr. now irrel b1 b2.
Qed.

Lemma TandS_proof_irr: forall hm1 hm2 a1 a2 b1 b2,
  hm1 = hm2 ->
  TandS f u hm1 a1 b1 = TandS f u hm2 a2 b2.
Proof.
  intros. generalize a1 a2 b1 b2. clear a1 a2 b1 b2.
  replace hm1 with hm2. intros. replace a1 with a2 by apply step_invariant_proof_irr. now irrel b1 b2.
Qed.

Lemma min_in_nat_calcT_proof_irr: forall hm1 hm2 w1 w2 nd1 nd2 a1 a2 b1 b2 c1 c2,
  !w1 = !w2 -> hm1 = hm2 ->
  !(!(min_in_nat idx nd1 (w1 :: !(calcT f u hm1 a1 b1)) c1)) =
  !(!(min_in_nat idx nd2 (w2 :: !(calcT f u hm2 a2 b2)) c2)).
Proof.
  intros. generalize c1 c2.
  replace (!(calcT f u hm1 a1 b1)) with (!(calcT f u hm2 a2 b2)); [intros; now apply min_in_nat_element_proof_irr | now apply calcT_proof_irr].
Qed.

Lemma min_in_nat_TandS_proof_irr: forall hm1 hm2 nd1 nd2 a1 a2 b1 b2 c1 c2,
  hm1 = hm2 ->
  !(!(min_in_nat idx nd1 (TandS f u hm1 a1 b1) c1)) =
  !(!(min_in_nat idx nd2 (TandS f u hm2 a2 b2) c2)).
Proof.
  intros. generalize c1 c2.
  replace (TandS f u hm1 a1 b1) with (TandS f u hm2 a2 b2); [intros; apply min_in_nat_proof_irr | now apply TandS_proof_irr].
Qed.


(*** FACTS ABOUT D and El in @i ***)

Lemma Pn_idx: (P f u (&@n) (?@n)) = idx.
Proof.
  rewrite (PF f u (&@n) (?@n)). unfold step, idx. rewrite <- firstn_all, pow_i, idx_len with (f:=f); auto.
Qed.

Lemma D_empty: (&@n).(D) = nil.
Proof.
  case n eqn:A. now simpl.
  rewrite <- pow_succ at 1. remember (@n0). unfold_step (&s).
  * copy e. rewrite Heqs, pow_i in e0; lia.
  * copy n2. rewrite Heqs, pow_i in n3; lia.
Qed.

Lemma D_empty_2: (&@(n-1)).(D) = nil.
Proof.
  assert (n-1 <= n) by lia. apply pow_i in H. pose f.(N).
  destruct (@(n-1)) eqn:N. case (D x) eqn:D; auto. destruct p. simpl in *.
  assert (In (n0,n1) ((n0,n1)::l)) as IN by apply in_eq. rewrite <- D in IN. copy IN. copy IN.
  apply (DP f u x s) in IN as []. apply (Db f u) in IN0 as [bi [xi [? [?] ] ] ]; auto. 2: lia.
  copy H3. assert (bi < n). { apply nth_error_len in H3. enow erewrite idx_len in H3. }
  assert (forall bid, bid < n -> nth_error idx bid = Some (b f x) -> bid = n-1). { intros bid SN ID. apply nth_error_nth with (d:=0) in ID.
  unfold b in ID. apply NoDup_nth in ID. 2: enow eapply idx_nodup. 2: enow erewrite idx_len. 2: rewrite idx_len with (f:=f); auto; lia. now rewrite <- H. }
  assert (bi = n-1) by now apply H7.
  assert (xi = n-1). { apply nth_error_len in H4. rewrite idx_len with (f:=f) in H4; auto; lia. }
  assert (n0 = b f x). { rewrite H8 in H3. rewrite H9 in H4. rewrite H3 in H4. now injection H4. }
  rewrite H10 in IN1. apply (DI f u x s) in IN1 as [bi' [xi' [? [?] ] ] ].
  assert (bi' < n). { apply nth_error_len in H12. enow unfold n; erewrite <- idx_len. }
  assert (xi' < n). { apply nth_error_len in H13. enow unfold n; erewrite <- idx_len. }
  assert (bi' = n-1) by now apply H7. lia.
Qed.

Lemma El_grows: forall hm v w,
  In (v, w) (&hm).(El) ->
  In (v, w) (&(step hm)).(El).
Proof.
  intros. unfold_step (&hm). case u; [unfold uniform_step | unfold tainted_step]; simpl; apply in_app; now left.
Qed.

Lemma El_grows_n: forall j v w,
  j < n ->
  In (v, w) (&@j).(El) ->
  In (v, w) (&@n).(El).
Proof.
  intros. pose (nj := n-j). replace j with (n-nj) in H0 by lia. generalize dependent nj.
  induction nj. now replace (n-0) with n by lia.
  destruct (n-S nj) eqn:A.
  * simpl. contradiction.
  * intro. apply El_grows in H0. rewrite pow_succ in H0. replace (S(S n0)) with (n-nj) in * by lia. auto.
Qed.

Lemma El_grows_b: forall hm v w,
  In (v, w) (&(step hm)).(El) ->
  ~ In (v, w) (&hm).(El) ->
  v = b f (&hm).
Proof.
  intros. unfold_step_in H (&hm); try contradiction.
  case u in H.
  + unfold uniform_step in H. simpl in H. apply in_app in H as []. contradiction. apply list_in_map_inv in H as [? [] ].
    destruct x. now unfold_tuples.
  + unfold tainted_step in H. simpl in H. apply in_app in H as []. contradiction. apply in_inv in H as []. unfold_tuples.
    now symmetry. contradiction.
Qed.

Lemma El_grows_inv: forall v w j (V: In v idx),
  j < n ->
  j >= !(index_nat idx v V) ->
  In (v, w) (El (&@n)) -> In (v, w) (El (&@(S j))).
Proof.
  intros. pose (n-j) as nj. assert (j < n) by lia.
  replace j with (n-nj) in * by lia.
  induction nj. lia.
  destruct (lt_dec nj n).
  2: { replace (S(n-S nj)) with 1 by lia. assert (n-nj<n) by lia. apply IHnj in H3; try lia. now replace (S(n-nj)) with 1 in H3 by lia. }
  destruct nj eqn:NJ. now replace (S (n-1)) with n by lia.
  assert (n - S n0 < n) by lia. apply IHnj in H3; try lia.
  assert (n > S n0) by lia.
  remember (S (n - S (S n0))). replace (S (n - S n0)) with (S n1) by lia.
  rewrite <- pow_succ in H3. edestruct (In_dec edge_eq_dec (v,w) (El (&@n1))); auto. apply El_grows_b in n2. 2: now replace n1 with (n-S n0) by lia.
  unfold b in n2. enough (n - S (S n0) >= n1) by lia. apply Arith_prebase.le_plus_minus_stt in H0. 
  rewrite H0. generalize V. rewrite n2. intros. rewrite (index_nth Nat.eq_dec); try rewrite pow_i; try lia. rewrite idx_len with (f:=f) at 1; auto; fold n; lia. enow eapply idx_nodup. 
Qed.

Lemma El_b: forall (hm: step_data_inv) v w,
  (&hm).(i) < n ->
  In (v, w) (El (&hm)) ->
  v << (b f (&hm)) in idx.
Proof.
  intros. destruct hm. simpl in *. apply (EP f u x s) in H0. now apply Pb in H0.
Qed.

Lemma b_not_in_El: forall (hm: step_data_inv) w,
  (&hm).(i) < n ->
  ~ In (b f (&hm), w) (El (&hm)).
Proof.
  intros. intro. apply El_b in H0; auto. apply (before_id Nat.eq_dec) in H0; auto. enow exploit idx_nodup.
Qed.

Lemma El_graph_edge: forall v w,
  In (v, w) (El (&@n)) <-> v → w in pcfl.
Proof.
  split; intros.
  * split. now unfold pcfl, el_graph, es. apply (EV f u (&@n) (?@n)) in H. now repeat rewrite result_vertex.
  * destruct H. now unfold pcfl, el_graph, es in H.
Qed.

Lemma El_filter_n: forall v V n', 
  let j := !(index_nat idx v V) in
  j < n' <= n ->
  filter (fun '(v',w) => v =? v') (El (&@n')) = filter (fun '(v',w) => v =? v') (El (&@(S j))).
Proof.
  intros. generalize dependent n'. induction n'; try lia; intros.
  destruct (Nat.lt_total j n') as [?|[|] ]; [| now subst | lia].
  assert (j < n' <= n) by lia. apply IHn' in H1. rewrite <- H1. rewrite <- pow_succ. remember (@n').
  assert (v <> b f (&@n')). { intro. unfold b in H2. rewrite pow_i in H2; try lia.
    assert (v = nth j idx 0) by (unfold j; symmetry; apply nth_index). rewrite H3 in H2.
    apply NoDup_nth in H2; [ lia | enow eapply idx_nodup | rewrite idx_len with (f:=f); auto; lia | rewrite idx_len with (f:=f); auto; lia ]. }
  unfold_step (&s). case u eqn:U;
    unfold uniform_step, tainted_step, El; rewrite filter_app;
    match goal with [ |- ?a ++ ?b = ?a ] => remember b as B; enough (bn: B = nil) by now rewrite bn, app_nil_r end;
    destruct B; try easy; assert (In p (p::B)) by apply in_eq; rewrite HeqB in H3.
  * apply filter_In in H3 as []. apply list_in_map_inv in H3 as [? [] ].
    destruct x, p. unfold_tuples. apply Nat.eqb_eq in H4. rewrite H3, Heqs in H4. now exfalso.
  * apply filter_In in H3 as []. simpl in H3. destruct H3; try contradiction.
    destruct p. unfold_tuples. apply Nat.eqb_eq in H4. rewrite <- H3, Heqs in H4. now exfalso.
Qed.

Lemma El_filter_j: forall v V,
  let j := !(index_nat idx v V) in 
  filter (fun '(v',w) => v =? v') (El (&@j)) = nil.
Proof.
  intros. destruct (filter _ _) eqn:L; auto.
  assert (In p (filter _ _)) by (rewrite L; apply in_eq).
  apply filter_In in H as []. destruct p.
  pose (EP f u (&@j) (?@j)). apply i in H.
  assert (j < n) by (unfold n; rewrite <- idx_len with (f:=f); auto; now apply index_len).
  apply Pb in H; [| rewrite pow_i; lia ]. apply Nat.eqb_eq in H0.
  assert (v = b f (&@j)) by (unfold b; rewrite pow_i; try lia; unfold j; symmetry; apply nth_index).
  rewrite <- H0, H2 in H. apply (before_id Nat.eq_dec) in H; [ now exfalso | now apply idx_nodup with (f:=f) ].
Qed.


Lemma El_successors_j: forall v V,
  let j := !(index_nat idx v V) in
  successors pcfl v = map snd (filter (fun '(v', _) => v =? v') (El (&@(S j)))).
Proof.
  intros. rewrite <- pow_succ. remember (@j) as h.
  match goal with [ |- ?a = ?b ] => remember a as left; remember b as right end.
  unfold successors, pcfl in Heqleft.
  remember ((fun '(v',w) => v =? v'): nat*nat -> bool) as g1. remember ((fun '(v',w) => vertex_dec pcfl w): nat*nat -> bool) as g2.
  rewrite filter_filter with (g:=g1) (h:=g2) in Heqleft.
  unfold es, el_graph in Heqleft. rewrite filter_same with (f:=g2), Heqg1 in Heqleft. rewrite El_filter_n with (V:=V) in Heqleft.
  rewrite Heqleft, Heqright, Heqh, Heqg1. now rewrite pow_succ.
  + enough (j < n) by lia. unfold n; rewrite <- idx_len with (f:=f); auto; now apply index_len.
  + intros [x1 x2]. intro. rewrite Heqg2. apply (EV f u (&@n) (?@n)) in H as [].
    apply result_vertex_iff in H0. now destruct (vertex_dec pcfl x2).
  + intros. rewrite Heqg1, Heqg2. unfold pcfl. now destruct x.
Qed.

Lemma El_successors_exact: forall v V a1 a2 a4 a5 a6 a7,
  v <> f.(exit) ->
  let j := !(index_nat idx v V) in
  successors pcfl v =
  if u v then 
    map (fun s => (!(!(min_in_nat idx a1 (s :: !(calcT f u (&@j) (?@j) a2)) ltac:(congruence))))) (!(calcS f u (&@j) (?@j) a4))
  else
    !(!(min_in_nat idx a5 (TandS f u (&@j) (?@j) a6) a7)) :: nil.
Proof.
  intros. rewrite El_successors_j with (V:=V). fold j.
  match goal with [ |- ?a = ?b ] => remember a as left; remember b as right end.
  rewrite <- pow_succ in Heqleft. remember (@j) as h in Heqleft.
  assert (j < n) by (pose (index_len Nat.eq_dec idx v V); unfold idx in l; rewrite idx_len with (f:=f) in l; auto; unfold n, j, index_nat; lia).
  assert (j = (i (&h))) by (rewrite Heqh, pow_i; lia).
  assert (v = b f (&h)) by (unfold b; rewrite <- H1; symmetry; apply nth_index).
  unfold_step_in Heqleft (&h).
  * assert (IL: length idx = length f.(g).(vs)) by (destruct IDX; now apply Permutation_length).
    assert (length (f.(g).(vs)) > 0) by (pose proof f.(VS); pose proof f.(N); clear Heqright a2 a4 a6 a7; destruct f.(g).(vs); [ destruct f.(GraphRTL.n); [auto | simpl in H3; congruence] | simpl; lia ]). 
    assert (is_exit f.(g) v) by (unfold b in H2; unfold idx in *; rewrite H2, e, <- idx_len with (f:=f), IL; eauto; apply top_sort_last_exit; eauto).
    destruct (f.(EXIT) v). exfalso. exact (H (H6 H4)).
  * case (u v) eqn:UV.
  + rewrite <- H2, UV in Heqleft.
    unfold uniform_step, El in Heqleft. rewrite filter_app, map_app in Heqleft. rewrite Heqleft.
    generalize n0 n1. rewrite Heqh. intros.
    replace (let (_, _, El) := & (@ j) in El) with (El (&@j)) by auto. unfold j. rewrite El_filter_j.
    simpl. rewrite Heqright.
    match goal with [ |- map snd (filter ?f1x (map ?f2x (map ?f3x ?a))) = map ?gx ?b ] => remember a as left'; remember b as right'; remember f1x as f1; remember f2x as f2; remember f3x as f3; remember gx as g end.
    replace left' with right' by (rewrite Heqleft', Heqright'; unfold j; now apply calcS_proof_irr).
    rewrite map_map. rewrite filter_same.
    - rewrite map_map. apply map_ext. intros.
      rewrite Heqf2, Heqf3, Heqg. now apply min_in_nat_calcT_proof_irr.
    - intros. apply list_in_map_inv in H3 as [? [] ]. destruct x. rewrite Heqf1. rewrite Heqf2 in H3. destruct (f3 x0) in H3. unfold_tuples.
      rewrite H3. unfold b, idx. rewrite pow_i; [setoid_rewrite nth_index at 1; apply Nat.eqb_refl |].
      enough (!(index_nat idx v V) < n) by (fold idx; lia). unfold n. erewrite <- idx_len. apply index_len.
  + rewrite <- H2, UV in Heqleft.
    unfold tainted_step, El in Heqleft. rewrite filter_app, map_app in Heqleft. rewrite Heqleft.
    generalize n0 n1. rewrite Heqh. intros. replace (let (_, _, El) := & (@ j) in El) with (El (&@j)) by auto. unfold j. rewrite El_filter_j.
    simpl. generalize dependent V. rewrite H2. intros. unfold b, idx. setoid_rewrite (index_nth Nat.eq_dec) with (l:=f.(GraphRTL.idx)) (d:=0) (i:=(i (&h))); auto.
    2: { rewrite <- H1. now rewrite idx_len. }
    fold idx. replace (nth (i (& h)) idx 0 =? nth (i (& (@ i (& h)))) idx 0) with true by (rewrite <- H1, pow_i; try lia; symmetry; apply Nat.eqb_refl).
    simpl. rewrite Heqright. erewrite min_in_nat_TandS_proof_irr; eauto.
Qed.


(*** BRANCH MAPPING: A MAP FROM EACH EDGE TO ITS NEW TARGET ***)

Section BranchMapping.

(* The new target of a vertex assuming it is tainted. *)
Program Definition tainted_target: forall v, vertex f.(g) v -> v <> f.(exit) -> V := fun v vv ve =>
  let i := index_nat idx v _ in
  min_in_nat idx (idx_nodup f) (TandS f u (&@i) (?@i) _) _.
Next Obligation.
  eapply idx_in; eauto.
Qed.
Next Obligation.
  destruct index_nat. simpl. apply nth_error_len in e. unfold idx in e; rewrite idx_len with (f:=f) in e; auto. unfold step. rewrite pow_i; lia.
Qed.
Next Obligation.
  unfold TandS. intro. apply app_eq_nil in H as []. apply Snonempty in H0. auto.
  destruct index_nat with (l:=idx) (x:=v) in |- *. copy e. simpl. apply nth_error_len in e. unfold idx in e; rewrite idx_len with (f:=f) in e; auto. unfold step; rewrite pow_i; try lia.
  destruct (Nat.eq_dec x (n-1)); try lia. epose proof (rtl_top_sort_exit f 0). intro. eapply nth_error_nth in e0. rewrite e1 in e0. unfold n, idx in e0. rewrite e0 in H1.
  congruence.
Qed.

(* The new target of any given edge after the algorithm. *)
Program Definition new_target: forall v w, v → w in f.(g) -> V := fun v w vw =>
  let i := index_nat idx v _ in
  if u v then
    min_in_nat idx (idx_nodup f) ([w] :: calcT f u (&@i) (?@i) _) _
  else
    tainted_target v _ _.
Next Obligation.
  enow eapply idx_in.
Qed.
Next Obligation.
  enow eapply idx_in.
Qed.
Next Obligation.
  destruct index_nat. simpl. unfold idx in e. apply nth_error_len in e. rewrite idx_len with (f:=f) in e; auto. unfold step. rewrite pow_i; lia.
Qed.
Next Obligation.
  destruct (Nat.eq_dec v f.(exit)); auto. subst. apply successors_spec with (w:=w) in vw; auto.
  pose (proj1 (f.(EXIT) f.(exit)) eq_refl). destruct i. rewrite H0 in vw. auto.
Qed.

(* The new successors of a u edge after the algorithm. *)
Program Definition uniform_successors: forall v, vertex f.(g) v -> v <> f.(exit) -> list V := fun v vv ve =>
  let succs := map_extra_id (successors f.(g) v) (edge f.(g) v) ltac:(intros; now apply successors_spec) in
  map (fun H => new_target v (proj1_sig H) (proj2_sig H)) succs.

Lemma new_successors_of_exit: 
  successors (pcfl) f.(exit) = nil.
Proof.
  remember (successors _ _) as S. destruct S; auto.
  assert (f.(exit) → v in pcfl) by (apply successors_spec; [now apply result_vertex_iff, f.(EXIT) | rewrite <- HeqS; apply in_eq]).
  now apply El_graph_edge, (EI f u (&@n) (?@n)), rtl_top_sort_exit_before in H.
Qed.

Lemma TandSnonempty: forall v a1 a2 a3,
  vertex f.(g) v ->
  v <> f.(exit) ->
  TandS f u (&@(!(index_nat idx v a1))) a2 a3 <> nil.
Proof.
  intros. unfold TandS. edestruct (!(calcT f u _ _ _) ++ !(calcS f u _ _ _)) eqn:A; try congruence;
  apply app_eq_nil in A as []. apply Snonempty in H2; auto.
  remember (index_nat _ _ _).
  assert (!s < n) by (rewrite Heqs; unfold n; rewrite <- idx_len with (f:=f); auto; apply index_len).
  rewrite pow_i; try lia. intro.
  assert (length (vs (g f)) = f.(GraphRTL.n)) by (rewrite f.(VS); apply seq_length).
  assert (v = (nth (length (vs (g f)) - 1) idx 0)) by (rewrite H5, <- H4, Heqs; symmetry; apply nth_index).
  copy IDX. unfold idx in H6. apply top_sort_last_exit with (d:=0) in IDX0;
  [rewrite <- H6 in IDX0 at 1; now apply f.(EXIT) in IDX0 | rewrite H5; apply f.(N)].
Qed.

Lemma new_successors_uniform: forall v
  (VV: vertex f.(g) v)
  (VE: v <> f.(exit)),
  u v = true ->
  successors pcfl v = uniform_successors v VV VE.
Proof.
  intros.
  assert (L: forall z, i (&@(!(index_nat idx v z))) < GraphRTL.n f) by
    (intro; eassert (!(index_nat idx v z) < n) by (unfold n; rewrite <- idx_len with (f:=f); auto; apply index_len);
    rewrite pow_i; auto; lia).
  erewrite El_successors_exact; auto.
  unfold uniform_successors, new_target. rewrite H. unfold calcS.
  match goal with [ |- map ?f ?a = map ?g ?b ] => remember f as f1; remember a as left; remember g as f2; remember b as right end.
  eassert ((b f (&@ (!(index_nat idx v ?[x])))) = v) by
    (unfold b; eassert (!(index_nat idx v ?x) < n) by (unfold n; rewrite <- idx_len with (f:=f); auto; apply index_len); erewrite pow_i; [apply nth_index | lia]).
  assert (length (successors f.(g) v) = length left) by (rewrite Heqleft; destruct map_extra_id; simpl; now rewrite <- H0, <- e, map_length). 
  assert (length (successors f.(g) v) = length right) by (rewrite Heqright; destruct (map_extra_id (successors f.(g) v) _ _); simpl; now rewrite <- e, map_length). 
  eapply map_equal_nth.
  * now rewrite <- H1, <- H2 at 1.
  * intros.
    assert (forall d1 d2, !(nth i left d1) = !(nth i right d2)) by
      (intros; rewrite Heqleft, Heqright, 2 (map_extra_id_nth nat Nat.eq_dec), H0; [apply nth_indep | | rewrite H0]; now rewrite H1 at 1).
    rewrite Heqf2, Heqf1. apply min_in_nat_calcT_proof_irr.
    + rewrite H4 at 1; enow simpl.
    + simpl. eassert (?x = new_target_obligation_1 _ _ _) by apply proof_irr. enow rewrite H5 by apply proof_irr.
  Unshelve.
  - enow eapply idx_nodup.
  - apply L.
  - enow apply TandSnonempty.
  - apply L.
  - enow eapply idx_nodup.
  - apply L.
  - enow eapply idx_in.
Qed.

Lemma new_successors_uniform_length: forall v
  (VV: vertex f.(g) v)
  (VE: v <> f.(exit)),
  u v = true ->
  length (successors pcfl v) = length (successors f.(g) v).
Proof.
  intros. rewrite new_successors_uniform with (VV:=VV) (VE:=VE); auto. unfold uniform_successors. rewrite map_length. destruct map_extra_id.
  copy e. eapply (f_equal) in e0. rewrite <- e0, map_length. now simpl.
Qed.

Lemma new_successors_tainted: forall v
  (VV: vertex f.(g) v)
  (VE: v <> f.(exit)),
  u v = false ->
  successors pcfl v = tainted_target v VV VE :: nil.
Proof.
  intros.
  assert (i (&@ (!(index_nat idx v (tainted_target_obligation_1 v VV)))) < GraphRTL.n f) by
   (remember (!(index_nat idx v _)); assert (n0 < n) by (unfold n; rewrite Heqn0, <- idx_len with (f:=f); auto; apply index_len); rewrite pow_i; unfold n; lia).
  erewrite El_successors_exact; auto. rewrite H.
  unfold tainted_target. enow erewrite min_in_nat_TandS_proof_irr.
  Unshelve.
  all: auto; (try enow eapply idx_nodup); enow apply TandSnonempty.
Qed.

End BranchMapping.

End AlgoFacts.