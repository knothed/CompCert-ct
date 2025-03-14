Require Import Common Coqlib Classical Datatypes.
Require Import AST Memory Registers Maps Values Events Globalenvs Smallstep Op Integers.
Require Import Graph GraphDual GraphRTL ListsExtra Before InfluenceRegion.
Require Import Smallstep Errors.
Require Import Permutation.


Ltac simpl_excl := match goal with
  | [ H: ?a = !(!(?b)) |- _ ] => destruct b; simpl in H; try rewrite H in *
  | [ H: !(!(?b)) = ?a |- _ ] => destruct b; simpl in H; try rewrite H in *
  | [ H: ?a = !(?b) |- _ ] => destruct b; simpl in H; try rewrite H in *
  | [ H: !(?b) = ?a |- _ ] => destruct b; simpl in H; try rewrite H in *
end.

Section Algorithm.

Variable f: GraphRTL.function.
Let idx := f.(idx).
Let IDX := f.(IDX).
Let n := f.(n).


Lemma idx_len: length idx = n.
Proof. now apply top_sort_len. Qed.

Lemma idx_nodup: NoDup idx.
Proof. now apply top_sort_nodup with f.(g). Qed.

Lemma idx_in: forall x, In x idx <-> vertex f.(g) x.
Proof. intro. now apply Graph.idx_in with (x:=x) in IDX. Qed.


Definition ipd := ipd f.(g) f.(exit) f.(EXIT) idx IDX.
Notation "x ∈ 'ir' ( c )" := (in_ir f.(g) f.(exit) f.(EXIT) idx IDX c x) (at level 50).
Notation "c1 ∩ c2" := (intersect f.(g) f.(exit) f.(EXIT) idx IDX c1 c2) (at level 50).
Notation "c1 ∩( cs )∩ c2" := (chain_via f.(g) f.(exit) f.(EXIT) idx IDX cs c1 c2) (at level 50).
Notation "c1 ∩...∩ c2" := (exists cs, chain_via f.(g) f.(exit) f.(EXIT) idx IDX cs c1 c2) (at level 50).


Variable uniform_cond: V -> bool.

Definition chain_inv := chain_inv f.(g) f.(exit) f.(EXIT) idx IDX uniform_cond.

(* Data and invariant before a loop execution. *)

Record step_data := mk_step_data {
  i: nat;
  D: list (nat*nat);
  El: list (nat*nat);
}.

Record step_invariant (hm: step_data) := mk_step_inv {
  I: hm.(i) <= n;
  P: list nat;
  PF: P = firstn hm.(i) idx;

  DV: forall v w, In (v,w) hm.(D) -> vertex f.(g) v /\ vertex f.(g) w;
  DP: forall v w, In (v,w) hm.(D) -> ~ In v P /\ ~ In w P;
  DI: forall v w, In (v,w) hm.(D) -> (v << w in idx);
  DT: forall v w, In (v,w) hm.(D) -> chain_inv v w;

  EV: forall v w, In (v,w) hm.(El) -> vertex f.(g) v /\ vertex f.(g) w;
  EP: forall v w, In (v,w) hm.(El) -> In v P;
  EI: forall v w, In (v,w) hm.(El) -> (v << w in idx);
}.

Section OneStep.

(*** PREREQUISITES ***)

Variable hm: step_data.
Variable inv: step_invariant hm.
Hypothesis I: hm.(i) < n.

Definition b := nth hm.(i) idx 0.
Lemma b_vertex: vertex f.(g) b.
Proof. intros. apply idx_in. unfold b. destruct inv. apply nth_In. rewrite idx_len. lia. Qed.

Lemma P_length: length (P hm inv) = hm.(i).
Proof.
  rewrite (PF hm inv). apply firstn_length_le. rewrite idx_len. lia.
Qed.

Lemma P_nth: forall j, j < hm.(i) -> nth_error (P hm inv) j = nth_error idx j.
Proof.
  rewrite (PF hm inv). symmetry. now apply firstn_nth.
Qed.

Lemma P_spec: forall j v,
  nth_error idx j = Some v -> 
  (In v (P hm inv) <-> j < hm.(i)).
Proof.
  intros. split; intro.
  * apply index_nat in H0 as []. assert (x < hm.(i)) by (apply nth_error_len in e; now rewrite <- P_length). copy H0. apply P_nth in H0.
    rewrite <- H in e at 1. rewrite e in H0 at 1. apply NoDup_nth_error in H0. lia. apply idx_nodup. now apply nth_error_len in H.
  * pose (P_nth j H0). rewrite <- e in H. now apply nth_error_In in H.
Qed.

Lemma Pb: forall v,
  In v (P hm inv) -> v << b in idx.
Proof.
  intros. unfold before. destruct (index_nat (P hm inv) v H). exists x, hm.(i).
  assert (x < hm.(i)) by (apply nth_error_len in e; now rewrite P_length in e).
  split; auto. split. rewrite P_nth in e; auto. unfold b. rewrite nth_or_error; auto. destruct inv. now rewrite idx_len.
Qed.

Lemma Pnotb: forall v,
  In v (P hm inv) -> v <> b.
Proof.
  intros. apply Pb in H. intro. subst. apply (before_id Nat.eq_dec) in H. auto. apply idx_nodup.
Qed.

Lemma P_vertex: forall v,
  In v (P hm inv) -> vertex f.(g) v.
Proof.
  intros. apply Pb in H as [? [? [? []]]]. apply nth_error_In in H0. now apply idx_in.
Qed.

Lemma P_nodup: NoDup (P hm inv).
Proof.
  rewrite (PF hm inv). apply NoDup_app_remove_r with (skipn hm.(i) idx). rewrite firstn_skipn. apply idx_nodup.
Qed.

Lemma Db: forall v w,
  In (v, w) (D hm) -> b <<= v in idx.
Proof.
  intros. copy H. apply (DV hm inv) in H0 as []. apply get_idx_in with (idx:=idx) in H0 as [iv]; auto.
  unfold beforeeq. exists hm.(i), iv. split.
  + apply P_spec in e. destruct (DP hm inv v w H) as []. destruct lt_dec with iv (i hm); try lia. apply e in l. apply H0 in l. now exfalso.
  + split; auto. unfold b. symmetry. apply nth_or_error. destruct inv. now rewrite idx_len.
Qed.

Definition successors_in (D: list (V*V)) (v: V) : list V :=
  map snd (filter (fun '(v',w) => (v' =? v)) D).

Lemma successors_in_sound: forall v w,
  vertex f.(g) v ->
  In w (successors_in hm.(D) v) ->
  vertex f.(g) w.
Proof.
  intros. unfold successors_in in H0. apply list_in_map_inv in H0 as [x []].
  apply filter_In in H1 as []. destruct x as [x1 x2]. apply (DV hm inv x1 x2) in H1 as [].
  subst. now simpl.
Qed.

Definition successors_in_spec: forall v w D,
  In w (successors_in D v) <-> In (v,w) D.
Proof.
  intros. split; intro.
  + apply list_in_map_inv in H as [e []]. apply filter_In in H0 as []. replace e with (v,w) in *; auto.
    destruct e. apply pair_equal_spec. split; [ symmetry; now apply Nat.eqb_eq | auto ].
  + remember ((fun '(v', _) => v' =? v): V*V -> bool) as g. assert (In (v,w) D0 /\ g (v,w) = true).
    { split. auto. rewrite Heqg. now apply Nat.eqb_eq. }
    apply filter_In with (f:=g) in H0. apply in_map with (f:=snd) in H0. simpl in H0. now rewrite Heqg in H0.
Qed.

Lemma successors_index: forall v w,
  vertex f.(g) v ->
  In w (successors f.(g) v) -> v << w in idx.
Proof.
  intros. apply successors_spec in H0; auto. now apply edge_before with (idx:=idx) in H0.
Qed.

Lemma successors_in_D_index: forall v w,
  vertex f.(g) v ->
  In w (successors_in hm.(D) v) -> v << w in idx.
Proof.
  intros. apply successors_in_spec in H0. now apply (DI hm inv) in H0.
Qed.

Hint Resolve idx_nodup successors_in_sound idx_in b_vertex idx_len: core.
Hint Rewrite successors_in_sound idx_in: core.


Notation "a <>? b" := (negb (a =? b)) (at level 10).

Lemma neq: forall a, a <>? a = true -> False.
Proof.
  intros. unfold negb in H. rewrite Nat.eqb_refl in H. congruence.
Qed.



Definition in_idx: Type := {x: V | In x idx}.

Definition calcT : {r: list in_idx | map (@proj1_sig V _) r = successors_in hm.(D) b}.
Proof.
  set (t := successors_in hm.(D) b).
  eset (r := map_extra_id t (fun v => In v idx) _). exact r.
  Unshelve.
  + intros. apply successors_in_sound in H; auto. now apply idx_in.
Defined.

Definition calcS : {r: list in_idx | map (@proj1_sig V _) r = successors f.(g) b}.
Proof.
  set (s := successors f.(g) b).
  eset (r := map_extra_id s (fun v => In v idx) _). exact r.
  Unshelve.
  + intros. replace s with (successors f.(g) b) in H; auto. apply successors_spec in H. apply idx_in. autopath. now apply b_vertex.
Defined.

Lemma in_calcS: forall s,
  In s (!calcS) -> In (!s) (successors f.(g) b).
Proof.
  unfold calcS. simpl. intros. match goal with [ H: In s (!(?r)) |- _ ] => remember r end.
  destruct s, s0. simpl in *. apply (f_equal (proj1_sig (P:=_))) in Heqs0. simpl in Heqs0. rewrite Heqs0 in H.
  now apply map_extra_id_In in H.
Qed.

Lemma in_calcT: forall t,
  In t (!calcT) -> In (!t) (successors_in hm.(D) b).
Proof.
  unfold calcT. simpl. intros. match goal with [ H: In t (!(?r)) |- _ ] => remember r end.
  destruct t, s. simpl in *. apply (f_equal (proj1_sig (P:=_))) in Heqs. simpl in Heqs. rewrite Heqs in H.
  now apply map_extra_id_In in H.
Qed.

Definition TandS : list in_idx := !(calcT) ++ !(calcS).

Lemma inT_after_b: forall r, In r (!calcT) -> b << !r in idx.
Proof.
  intros. apply in_calcT, successors_in_spec in H. now apply (DI hm inv).
Qed.

Lemma inS_after_b: forall r, In r (!calcS) -> b << !r in idx.
Proof.
  intros. apply in_calcS, successors_spec in H; auto. enow eapply edge_before in H.
Qed.

Lemma inT_not_b: forall r, In r (!calcT) -> b <> !r.
Proof.
  intros. apply inT_after_b in H. now apply (before_id_neq Nat.eq_dec) in H.
Qed.

Lemma inS_not_b: forall r, In r (!calcS) -> b <> !r.
Proof.
  intros. apply inS_after_b in H. now apply (before_id_neq Nat.eq_dec) in H.
Qed.

Lemma inTandS_not_b: forall r, In r (TandS) -> b <> !r.
Proof.
  intros. unfold TandS in H. now apply in_app in H as []; [apply inT_not_b | apply inS_not_b].
Qed.

Lemma inT_idx: forall r, In r (!calcT) -> In (!r) idx.
Proof.
  intros. apply inT_after_b in H. now apply before_in in H as [].
Qed.

Lemma inS_idx: forall r, In r (!calcS) -> In (!r) idx.
Proof.
  intros. apply inS_after_b in H. now apply before_in in H as [].
Qed.

Lemma SingleReturn:
  forall v, vertex f.(g) v -> (v = nth (length idx - 1) idx 0 <-> successors f.(g) v = nil).
Proof.
  intros.
  assert (length f.(g).(vs) > 0). { rewrite f.(VS), seq_length. apply f.(N). }
  eapply top_sort_last_exit in H0; eauto. rewrite f.(VS), seq_length in H0. fold n in H0. fold idx in H0. rewrite <- idx_len in H0.
  apply f.(EXIT) in H0. rewrite H0. rewrite f.(EXIT). unfold is_exit. easy.
Qed.

Lemma Snonempty: hm.(i) <> n-1 -> !(calcS) <> nil.
Proof.
  intros. unfold calcS. enough (successors f.(g) b <> nil) by now apply map_extra_id_nonnil.
  destruct (SingleReturn b b_vertex). destruct (successors f.(g) b); try congruence.
  exfalso. pose (H1 eq_refl). unfold b in e. pose proof idx_nodup.
  rewrite NoDup_nth in H2. specialize H2 with hm.(i) (n-1). rewrite idx_len in *.
  assert (hm.(i) < n) by (destruct inv; lia). assert (n-1 < n) by (pose f.(N); lia).
  pose (H2 H3 H4 e). lia.
Qed.

Definition list_except (x: V) (l: list V) := filter (fun t => t <>? x) l.
Definition edges_from (x: V) (to: list V) := map (fun v => (x, v)) to.
Definition remove_from_b (es: list (V*V)) := filter (fun '(v,w) => v <>? b) es.

Notation "# l" := (map (fun a => !a) l) (at level 20).

Lemma hash_spec: forall a (l: list in_idx),
  In a (#l) -> {a': in_idx | In a' l /\ !a' = a}.
Proof.
  intros.
  destruct (index_nat (#l) a H) as [i].
  destruct (nth_error l i) eqn:J.
  * exists i0. split. now apply nth_error_in in J. copy e. copy J. eapply nth_error_nth in e0, J0. intros.
    rewrite map_nth in e0. now erewrite J0 in e0. Unshelve. exact i0.
  * assert (i < length (#l)) by (now apply nth_error_len in e). rewrite map_length in H0. apply nth_error_Some in J; auto. now exfalso.
Qed.

Lemma hash_spec_inv: forall A (P: A -> Prop) (x: A) (p: P x) l,
  In (exist P x p) l -> In x (#l).
Proof.
  intros. replace x with (!(exist P0 x p)) by auto. now apply in_map.
Qed.

Lemma hash_calcT: #!calcT = successors_in hm.(D) b.
Proof.
  unfold calcT. remember (map_extra_id _ _ _). destruct s. now simpl.
Qed.

Lemma hash_calcS: #!calcS = successors f.(g) b.
Proof.
  unfold calcS. remember (map_extra_id _ _ _). destruct s. now simpl.
Qed.

Lemma hash_TandS: #TandS = successors_in hm.(D) b ++ successors f.(g) b.
Proof.
  unfold TandS. destruct calcT, calcS. simpl. rewrite map_app. now rewrite e, e0 at 1.
Qed.

(*** ALGORITHM DEFINITION ***)

Program Definition uniform_step : step_data :=
  let nexts := map (fun s => (!s, !(!(min_in_nat idx _ (s::!calcT) _)))) (!calcS) in
  let ds '(s, next) := edges_from next (list_except next (s::#(!calcT))) in
  let newDs := flat_map ds nexts in
  let newEs := map (fun '(_, next) => (b, next)) nexts in
  mk_step_data (S hm.(i)) (remove_from_b (hm.(D) ++ newDs)) (hm.(El) ++ newEs).

Program Definition tainted_step (neq: hm.(i) <> n-1) : step_data :=
  let next := min_in_nat idx _ TandS _ in
  let newDs := edges_from (!next) (list_except (!next) (#TandS)) in
  let newE := (b, !next) in
  mk_step_data (S hm.(i)) (remove_from_b (hm.(D) ++ newDs)) (hm.(El) ++ newE::nil).
Next Obligation.
  unfold TandS. destruct (!calcT ++ !calcS) eqn:A; try congruence.
  apply app_eq_nil in A as []. now apply Snonempty in H0.
Qed.

Definition pcfl_step : step_data :=
  if Nat.eq_dec hm.(i) (n-1) then
    mk_step_data n nil hm.(El) else
  if (uniform_cond b) then
    uniform_step
  else
    tainted_step ltac:(auto).


(*** INVARIANT PROOFS ***)

Ltac unfold_In_D H := simpl in H; unfold remove_from_b in H; apply filter_In in H as []; apply in_app in H as [].

Ltac unfold_In_uniform_D H := let H1 := fresh in apply in_flat_map in H as [[] [H1]]; let H2 := fresh in apply list_in_map_inv in H1 as [y [H2]];
                                        unfold edges_from in H; apply list_in_map_inv in H as [x []].


Lemma DV_uniform: forall v w,
  In (v, w) (D uniform_step) -> vertex f.(g) v /\ vertex f.(g) w.
Proof.
  intros v w H. unfold_In_D H.
  + now apply (DV hm inv).
  + unfold_In_uniform_D H. apply inS_idx in H1.
    unfold_tuples.
    assert (forall w, In x (list_except w (#(!calcT))) -> In x idx). { intros W HY. unfold list_except in HY. apply filter_In in HY as [HY]. apply list_in_map_inv in HY as [? [R HY]]. apply inT_idx in HY. now rewrite <- R in HY. }
    assert (In x idx). { case negb in H3. apply in_inv in H3 as []. now subst. eapply H6; eauto. eapply H6; eauto. }
    replace x with w in *. split. 2: now apply idx_in.
    repeat simpl_excl. subst. now apply idx_in.
Qed.

Lemma DV_tainted: forall v w x,
  In (v, w) (D (tainted_step x)) -> vertex f.(g) v /\ vertex f.(g) w.
Proof.
  intros v w ? H. unfold_In_D H.
  + now apply (DV hm inv).
  + unfold edges_from, list_except in H. apply list_in_map_inv in H as [y []].
    unfold_tuples. split.
    - repeat simpl_excl. now apply idx_in.
    - apply filter_In in H1 as []. unfold TandS in H1. apply list_in_map_inv in H1 as [? []]. repeat simpl_excl. subst. now apply idx_in.
Qed.

Lemma DP_shared: forall v w,
  In (v, w) (D hm) -> v <>? b = true -> ~ In v (P hm inv ++ b :: nil) /\ ~ In w (P hm inv ++ b :: nil).
Proof.
  intros. copy H. apply (DP hm inv) in H as []. split; intro IN; apply in_app in IN as []; auto.
  * simpl in H2. destruct H3; [subst|contradiction]. unfold negb in H0. now rewrite Nat.eqb_refl in H0.
  * replace w with b in *. 2: { simpl in H3. now destruct H3. } copy H1. apply Db in H1. apply (DI hm inv) in H4. apply beforeeq_swap in H1. now apply H1 in H4. exact Nat.eq_dec. apply idx_nodup.
Qed.

Lemma DP_uniform: forall v w,
  In (v, w) (D uniform_step) -> ~ In v (P hm inv ++ b :: nil) /\ ~ In w (P hm inv ++ b :: nil).
Proof.
  intros v w H. unfold_In_D H.
  + apply DP_shared; auto.
  + unfold_In_uniform_D H. split; intro IN.
    * apply in_app in IN as []; auto.
    ** unfold_tuples. simpl_excl. simpl_excl. destruct a. apply in_inv in H7 as [].
     - apply inS_after_b in H1. subst. simpl in H1. apply Pb in H4. apply before_unique in H1; auto.
     - apply inT_after_b in H7. subst. simpl in H7. apply Pb in H4. apply before_unique in H7; auto.
    ** apply in_inv in H4 as []; auto. subst. now apply neq in H0.
    * unfold_tuples. assert (In w (list_except v1 (#(!calcT))) -> False).
      { intros. apply filter_In in H6 as []. apply list_in_map_inv in H6 as [? []]. apply inT_after_b in H8. rewrite <- H6 in H8.
        apply in_app in IN as []. apply Pb in H9. apply before_unique in H9; auto.
        apply in_inv in H9 as []; auto. subst. now apply (before_id Nat.eq_dec) in H8. }
      case (v0 <>? v1) in *. apply in_inv in H3 as []. subst. apply inS_after_b in H1.
      apply in_app in IN as []. apply Pb in H. apply before_unique in H1; auto.
      apply in_inv in H as []; auto. rewrite H in H1. now apply (before_id Nat.eq_dec) in H1.
      subst. now apply H6 in H3. subst. now apply H6 in H3.
Qed.

Lemma DP_tainted: forall v w x,
  In (v, w) (D (tainted_step x)) -> ~ In v (P hm inv ++ b :: nil) /\ ~ In w (P hm inv ++ b :: nil).
Proof.
  intros v w x H. unfold_In_D H.
  + apply DP_shared; auto.
  + unfold edges_from, list_except in H. apply list_in_map_inv in H as [y []].
    assert (forall a, In a TandS -> ~ In (!a) (P hm inv ++ b :: nil)).
    - intros. intro. apply in_app in H2 as []; [ apply inT_after_b in H2 | apply inS_after_b in H2 ];
          (apply in_app in H3 as []; [ apply Pb in H3; now apply before_unique in H3 | apply in_inv in H3 as []; auto; rewrite H3 in H2; now apply (before_id Nat.eq_dec) in H2 ]).
    - unfold_tuples. split.
     * match goal with [ H: v = !(!(?x)) |- _ ] => remember x end. destruct s, x0. simpl in H. destruct a. copy i1. apply H2 in i2. simpl in i2. now subst.
     * apply filter_In in H1 as []. apply list_in_map_inv in H1 as [? []]. subst. now apply H2 in H5.
Qed.

Lemma DI_tainted: forall v w x,
  In (v, w) (D (tainted_step x)) -> v << w in idx.
Proof.
  intros v w x H. unfold_In_D H.
  + now apply (DI hm inv).
  + unfold edges_from, list_except in H. apply list_in_map_inv in H as [y []]. unfold_tuples.
    match goal with [ H: v = !(!(?x)) |- _ ] => remember x end. destruct s, x0. destruct a.
    assert (In w (#TandS)) by (apply filter_In in H1 as []; now subst).
    apply b0 in H3. simpl in H3, H. rewrite H. apply (beforeeq_split Nat.eq_dec) in H3 as []; auto.
    apply filter_In in H1 as []. simpl in H4. rewrite <- H2, H3 in H4. now apply neq in H4.
Qed.

Lemma DI_uniform: forall v w,
  In (v, w) (D uniform_step) -> v << w in idx.
Proof.
  intros v w H. unfold_In_D H.
  + now apply (DI hm inv).
  + unfold_In_uniform_D H. unfold_tuples.
    assert (forall w, In w (y::!calcT) -> v <<= !w in idx). { simpl_excl. destruct a. intros. destruct w0. apply in_map with (f:=fun a => !a) in H8. apply H7 in H8. now subst. }
    assert (In w (!y::#(!calcT))).
    { rewrite H4, <- H2. case (v0 <>? v1) in H3. apply in_inv in H3 as []. rewrite <- H3. simpl. now left. apply filter_In in H3 as []. now apply in_cons. apply filter_In in H3 as []. now apply in_cons. }
    replace (!y :: #(!calcT)) with (#(y :: !calcT)) in H7. 2: now simpl. apply hash_spec in H7 as [w' []].
    apply H6 in H7. apply (beforeeq_split Nat.eq_dec) in H7 as []. 2: now subst.
    case (v0 <>? v1) eqn:E in H3.
    * apply in_inv in H3 as [].
    - rewrite H3, <- H4, <- H8, <- H in E. rewrite H7 in E. now apply neq in E.
    - apply filter_In in H3 as []. rewrite <- H4, <- H8, <- H, H7 in H9. now apply neq in H9.
    * apply filter_In in H3 as []. rewrite <- H4, <- H8, <- H, H7 in H9. now apply neq in H9.
Qed.

Lemma DT_D_D: forall v w,
  In v (successors_in (D hm) b) ->
  In w (successors_in (D hm) b) ->
  chain_inv v w.
Proof.
  intros.
  apply successors_in_spec in H; copy H; apply (DT hm inv) in H.
  apply successors_in_spec in H0; copy H0; apply (DT hm inv) in H0.
  unfold chain_inv, InfluenceRegion.chain_inv in *; decompose [ex and] H; decompose [ex and] H0.
  exists x0, x3, (rev x1 ++ x :: x2 :: x4). repeat split; auto.
  - intros. repeat destruct H10. apply H4, in_cons, in_eq. apply H8, in_cons, in_eq.
    apply in_app in H10 as []. apply in_rev in H10. now apply H4, in_cons, in_cons. repeat destruct H10.
    subst. apply H4, in_eq. apply H8, in_eq. subst. now apply H8, in_cons, in_cons.
  - assert (x ∩ x2) by now exists b.
    eapply chain_trans_full with (c2:=x).
    + now apply chain_sym_full.
    + now constructor.
Qed.

Lemma DT_D_S: forall v w,
  In v (successors_in (D hm) b) ->
  In w (successors (g f) b) ->
  chain_inv v w.
Proof.
  intros.
  apply successors_spec in H0; auto.
  apply successors_in_spec in H; copy H; apply (DT hm inv) in H.
  apply chain_inv_sym. apply chain_inv_direct_edge with (v:=b); auto. apply DI in H1; auto.
Qed.

Lemma DT_S_S: forall v w,
  In v (successors (g f) b) ->
  In w (successors (g f) b) ->
  uniform_cond b = false ->
  chain_inv v w.
Proof.
  intros.
  exists b, b, nil. repeat split; auto.
  - intros. now repeat destruct H2.
  - now apply ir_edge_head, successors_spec.
  - now apply ir_edge_head, successors_spec.
  - apply chain_refl_full. auto. intro. apply EXIT in H2 as []. now rewrite H3 in H.
Qed.

Lemma DT_tainted: forall v w x,
  In (v, w) (D (tainted_step x)) ->
  uniform_cond b = false ->
  chain_inv v w.
Proof.
  intros. unfold_In_D H.
  + now apply (DT hm inv).
  + unfold edges_from, list_except in H. apply list_in_map_inv in H as [y []]. unfold_tuples.
    match goal with [ H: v = !(!(?x)) |- _ ] => remember x end. destruct s, x0. destruct a. simpl in *. subst.
    assert (In x0 (#TandS)) by enow eapply hash_spec_inv.
    assert (In y (#TandS)) by (apply filter_In in H2 as []; now subst).
    rewrite hash_TandS in H, H3. apply in_app in H as []; apply in_app in H3 as [].
    * now apply DT_D_D.
    * now apply DT_D_S.
    * now apply chain_inv_sym, DT_D_S.
    * now apply DT_S_S.
Qed.

Lemma DT_uniform: forall v w,
  In (v, w) (D uniform_step) -> chain_inv v w.
Proof.
  intros. unfold_In_D H.
  + now apply (DT hm inv).
  + unfold_In_uniform_D H. unfold_tuples. subst.
    destruct min_in_nat, a, x0. simpl in *. assert (In y TandS) by enow apply in_app.
    destruct i0.
    * subst y. apply in_calcS in H1. simpl in *.
      case negb eqn:?; [now apply neq in Heqb1 |].
      apply filter_In in H3 as []. rewrite hash_calcT in H2.
      now apply chain_inv_sym, DT_D_S.
    * destruct y. apply in_calcS in H1. apply in_calcT in H2. simpl in *.
      case negb eqn:?.
      - assert (x1 <> x0) by (intro; subst; now apply neq in Heqb1).
        destruct H3. subst. now apply DT_D_S.
        apply filter_In in H3 as []. rewrite hash_calcT in H3. now apply DT_D_D.
      - apply filter_In in H3 as []. rewrite hash_calcT in H3. now apply DT_D_D.
Qed.

Lemma EV_tainted: forall v w x,
  In (v, w) (El (tainted_step x)) -> vertex f.(g) v /\ vertex f.(g) w.
Proof.
  intros v w x H. simpl in H. apply in_app in H as [].
  + now apply (EV hm inv).
  + simpl in H. destruct H; try contradiction. unfold_tuples. repeat simpl_excl. subst. split. apply b_vertex. now apply idx_in.
Qed.

Lemma EV_uniform: forall v w,
  In (v, w) (El uniform_step) -> vertex f.(g) v /\ vertex f.(g) w.
Proof.
  intros v w H. unfold uniform_step in H. apply in_app in H as [].
  + now apply (EV hm inv).
  + apply list_in_map_inv in H as [? []]. apply list_in_map_inv in H0 as [? []]. rewrite H0 in H. unfold_tuples. split. subst. apply b_vertex.
    match goal with [ H: w = !(!(?x)) |- _ ] => remember x end. repeat simpl_excl. now apply idx_in.
Qed.

Lemma EP_tainted: forall v w x,
  In (v, w) (El (tainted_step x)) -> In v (P hm inv ++ b::nil).
Proof.
  intros v w x H. simpl in H. apply in_app in H as [].
  + apply (EP hm inv) in H. apply in_app. now left.
  + apply in_inv in H as []. unfold_tuples. apply in_app. right. subst. now apply in_eq. simpl in H. contradiction.
Qed.

Lemma EP_uniform: forall v w,
  In (v, w) (El uniform_step) -> In v (P hm inv ++ b::nil).
Proof.
  intros v w H. unfold uniform_step in H. apply in_app in H as [].
  + apply (EP hm inv) in H. apply in_app. now left.
  + apply list_in_map_inv in H as [? []]. apply list_in_map_inv in H0 as [? []]. rewrite H0 in H. unfold_tuples. subst. apply in_app. right. now apply in_eq.
Qed.

Lemma EI_tainted: forall v w x,
  In (v, w) (El (tainted_step x)) -> v << w in idx.
Proof.
  intros v w x H. simpl in H. apply in_app in H as [].
  + now apply (EI hm inv) in H.
  + destruct H; try contradiction. unfold_tuples.
    simpl_excl. destruct a. unfold TandS in H1. apply in_app in H1 as []; [apply inT_after_b in H1 | apply inS_after_b in H1]; now subst.
Qed.

Lemma EI_uniform: forall v w,
  In (v, w) (El uniform_step) -> v << w in idx.
Proof.
  intros v w H. unfold uniform_step in H. apply in_app in H as [].
  + now apply (EI hm inv) in H.
  + apply list_in_map_inv in H as [? []]. apply list_in_map_inv in H0 as [? []]. destruct x. unfold_tuples.
    simpl_excl. destruct a. destruct H4; [apply inS_after_b in H1 | apply inT_after_b in H4]; now subst.
Qed.

Definition invariant_correct: forall hm',
  pcfl_step = hm' -> step_invariant hm'.
Proof.
  intros. unfold pcfl_step in H. rewrite <- H. clear H.

  case (Nat.eq_dec (i hm) (n-1)) eqn:A.
  * constructor 1 with (P:=(P hm inv) ++ b::nil).
  + unfold i. lia.
  + unfold i. rewrite (PF hm inv). unfold b. rewrite firstn_app_nth. now replace (S hm.(i)) with n by lia. rewrite idx_len. lia.
  + now intros.
  + now intros.
  + now intros.
  + now intros.
  + apply (EV hm inv).
  + intros. apply in_or_app. left. now apply (EP hm inv) with (w:=w).
  + apply (EI hm inv). 
  * constructor 1 with (P:=(P hm inv) ++ b::nil).
  + case uniform_cond; auto.
  + unfold i. rewrite (PF hm inv). case uniform_cond; [unfold uniform_step | unfold tainted_step];  unfold b; rewrite firstn_app_nth; auto; rewrite idx_len; lia.
  + intros. case uniform_cond in H; [now apply DV_uniform | now apply DV_tainted with (x:=n0)].
  + intros. case uniform_cond in H; [now apply DP_uniform | now apply DP_tainted with (x:=n0)].
  + intros. case uniform_cond in H; [now apply DI_uniform | now apply DI_tainted with (x:=n0)].
  + intros. case uniform_cond eqn:? in H; [ now apply DT_uniform | now apply DT_tainted with (x:=n0)].
  + intros. case uniform_cond in H; [now apply EV_uniform | now apply EV_tainted with (x:=n0)].
  + intros. case uniform_cond in H; [now apply EP_uniform with (w:=w) | now apply EP_tainted with (x:=n0) (w:=w)].
  + intros. case uniform_cond in H; [now apply EI_uniform | now apply EI_tainted with (x:=n0)].
Qed.

End OneStep.

(*** THE FULL ALGORITHM ***)

Notation "[[ e ]]" := (existT _ e _).
Notation "& x" := (projT1 x) (at level 10).
Notation "? x" := (projT2 x) (at level 10).

(* Algorithm data together with the loop invariant. *)
Definition step_data_inv: Type := {hm: step_data & step_invariant hm}.

Definition step_empty: step_data_inv.
Proof.
  exists (mk_step_data 0 nil nil).
  constructor 1 with (P:=nil); auto; try now simpl. unfold i. lia.
Defined.

Program Definition step_inv_step (hm: step_data_inv) : step_data_inv :=
  if (Nat.eq_dec (&hm).(i) n) then hm else
  let step := pcfl_step (&hm) _ _ in [[step]].
Next Obligation. destruct hm. now simpl. Qed.
Next Obligation. destruct hm. pose (I x s). simpl in *. lia. Qed.
Next Obligation. eapply invariant_correct; eauto. Qed.

Fixpoint pow {A} (f: A -> A) n x := match n with
  | 0 => x
  | S i => pow f i (f x)
end.

Notation "@ i" := (pow step_inv_step i step_empty) (at level 30).

Definition el_graph (hm: step_data_inv) : G := mkG f.(g).(vs) f.(g).(nodup) (&hm).(El).

Definition pcfl := el_graph (@n).

End Algorithm.
