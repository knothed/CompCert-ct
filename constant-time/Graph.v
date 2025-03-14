Require Import Common Coqlib Classical Datatypes BinPos.
Require Import Permutation.
Require Import ListsExtra Before.

Definition V := nat.

Record G': Type := mkG {
  vs: list nat;
  nodup: NoDup vs;
  es: list (nat*nat)
}.
Definition G: Type := G'.

Section Graph.
Variable g: G.

Definition vertex (v: V) := In v g.(vs).
Definition edge (v w : V) := In (v,w) g.(es) /\ vertex v /\ vertex w.

Infix "→" := edge (at level 50).

Reserved Infix "→*" (at level 50).

Inductive path: V -> V -> Prop :=
  | path_refl: forall v, vertex v -> v →* v
  | path_left: forall u v w, (u → v) -> (v →* w) -> (u →* w)
where "v →* w" := (path v w).

Lemma edge_eq_dec: forall x y: nat*nat, {x = y} + {~x = y}.
Proof.
  intros [a b] [c d]. destruct Nat.eq_dec with a c, Nat.eq_dec with b d. auto.
  all: right; injection; intros; lia.
Defined.

Lemma vertex_dec: forall v, {vertex v} + {~ vertex v}.
Proof.
  unfold vertex. intro. apply in_dec. apply Nat.eq_dec.
Defined.

Lemma edge_dec: forall v w, {v → w} + {~ v → w}.
Proof.
  intros. destruct (vertex_dec v), (vertex_dec w).
  destruct (@in_dec (prod nat nat) edge_eq_dec (v,w) g.(es)).
   left; constructor; auto.
   right; now intros [].
  all: right; now intros [_ []].
Defined.

Ltac autopath :=
  match goal with
   | [ |- (?v →* ?v) ] => constructor; auto; try autopath
   | [ H: ?v → ?w |- vertex ?w ] => let I := fresh in destruct H as [_ [_ I]]; exact I
   | [ H: ?v → ?w |- vertex ?v ] => let I := fresh in destruct H as [_ [I _]]; exact I
   | [ H: ?u → ?v |- ?u →* ?v ] => constructor 2 with v; [exact H | autopath]
   | [ H1: ?u → ?v, H2: ?v →* ?w |- ?u →* ?w ] => constructor 2 with v; [exact H1 | exact H2]
  end.

Lemma path_right u v w: (u →* v) -> (v → w) -> (u →* w).
Proof.
  intros. induction H; [| pose (IHpath H0) ]; autopath.
Qed.

Lemma path_concat {u v w: V} (p: u →* v) (q: v →* w) : u →* w.
Proof.
 induction p; auto. constructor 2 with v; auto.
Qed.

Lemma path_vertex_right u v: (u →* v) -> vertex v.
Proof.
  now induction 1.
Qed.

(*** SUCCESSORS AND PREDECESSORS ***)

(* Sucessors are in the order of added edges (and can contain a vertex multiple times)
   because the order of added edges is important for representing branches. *)
Definition successors (v: V): list V :=
  List.map snd (List.filter (fun '(v',w) => andb (v =? v') (vertex_dec w)) g.(es)).

Lemma successors_spec: forall v w,
  vertex v -> In w (successors v) <-> v → w.
Proof.
  intros. split; intro.
  + unfold successors in H0. eapply list_in_map_inv with (f:=snd) in H0 as [e [S H0]].
    apply filter_In in H0 as [I F].
    assert (e = (v,w)). { destruct e. simpl in S. apply andb_prop in F as []. apply Nat.eqb_eq in H0. auto. }
    constructor. now rewrite <- H0. destruct e. replace v0 with w in *. apply andb_prop in F as [F].
    split; [auto | now destruct vertex_dec].
  + destruct H0. unfold successors. replace w with (snd (v,w)). apply in_map.
    apply filter_In. split. auto. apply andb_true_iff. split. apply Nat.eqb_eq. now unfold fst. destruct H1. now destruct vertex_dec. now unfold snd.
Qed.


Definition predecessors (v: V): list V :=
  List.map fst (List.filter (fun '(w,v') => andb (v =? v') (vertex_dec w)) g.(es)).

Lemma predecessors_spec: forall v w,
  vertex v -> In w (predecessors v) <-> w → v.
Proof.
  intros. split; intro.
  + unfold predecessors in H0. eapply list_in_map_inv with (f:=fst) in H0 as [e [S H0]].
    apply filter_In in H0 as [I F].
    assert (e = (w,v)). { destruct e. simpl in S. apply andb_prop in F as []. apply Nat.eqb_eq in H0. auto. }
    constructor. now rewrite <- H0. destruct e. replace v0 with w in *. apply andb_prop in F as [F].
    split; [now destruct vertex_dec | auto].
  + destruct H0. unfold predecessors. replace w with (fst (w,v)). apply in_map.
    apply filter_In. split. auto. apply andb_true_iff. split. apply Nat.eqb_eq. now unfold fst. destruct H1. now destruct vertex_dec. now unfold snd.
Qed.


(*** TRACES ***)

(* Path with a trace of taken nodes in between *)
Reserved Notation "v →( t )→* w" (at level 10).
Inductive trace: V -> V -> list V -> Prop :=
  | trace_refl: forall v, vertex v -> (v →(v::nil)→* v)
  | trace_left: forall u v w t, (u → v) -> (v →(t)→* w) -> (u →(u::t)→* w)
where "v →( t )→* w" := (trace v w t).

Ltac autotrace :=
  match goal with
   | [ |- (?v →(?v::nil)→* ?v) ] => constructor; auto; try autopath
   | [ H: ?u → ?v |- ?u →(?u::?v::nil)→* ?v ] => constructor 2 with v; [exact H | autotrace]
   | [ H1: ?u → ?v, H2: ?v →* ?w |- ?u →* ?w ] => constructor 2 with v; [exact H1 | exact H2]
   | [ H1: ?u → ?v, H2: ?v →(?t)→* ?w |- ?u →(?u::?t)→* ?w ] => constructor 2 with v; [exact H1 | exact H2]
  end.

(* Alternatively we could use trace to define path u v := exists t, trace u t v. *)

Lemma trace_path: forall {u v t}, u →(t)→* v -> u →* v.
Proof.
  induction 1; autopath.
Qed.

Lemma path_trace: forall {u v}, u →* v -> exists t, u →(t)→* v.
Proof.
  intros. induction H.
   - exists (v::nil). now constructor.
   - destruct IHpath as [t T]. exists (u::t). autotrace.
Qed.

Lemma trace_right u v w t: (u →(t)→* v) -> (v → w) -> (u →(t++w::nil)→* w).
Proof.
  intros. induction H; simpl; [| pose (IHtrace H0) ]; autotrace.
Qed.

Lemma trace_right_inv u w t:
  length t > 1 ->
  (u →(t)→* w) ->
  exists v t', u →(t')→* v /\ v → w /\ t = t'++w::nil.
Proof.
  intros. induction H0. simpl in H; lia.
  inv H1.
  * exists u, (u::nil). repeat (split; auto); autotrace.
  * exploit IHtrace; [inv H3; simpl; lia | intros [w' [t' [? [?]]]]].
    exists w', (u::t'). repeat (split; auto). autotrace.
    now rewrite H5, app_comm_cons.
Qed. 

Lemma trace_right_ind:
  forall P: V -> V -> list V -> Prop,
  (forall v, vertex v -> P v v (v :: nil)) ->
  (forall u v w t, u →(t)→* v -> v → w -> P u v t -> P u w (t++w::nil)) ->
  forall v w t, v →(t)→* w -> P v w t.
Proof.
  intros. generalize dependent v. generalize dependent w. induction t using list_ind_rev.
  * intros. inv H1.
  * intros. inv H1. now apply H. copy H6. inv H6.
    - replace (v::w::nil) with ((v::nil)++w::nil) by auto. apply H0 with (v:=v); auto. autotrace. apply H; autopath.
    - apply trace_right_inv in H1 as [w' [t' [? [?]]]]. 2: { inv H5; simpl; lia. }
      assert (x=w). { apply (f_equal (fun a => last a 0)) in H7, H2. simpl in H7, H2. rewrite H7 in H2. now rewrite 2 last_last in H2. }
      assert (t = v::t'). { rewrite H7, H8, app_comm_cons in H2. now apply app_inj_tail in H2. }
      rewrite H2, H8. apply H0 with (v:=w'); [ rewrite H9; autotrace | auto | apply IHt; rewrite H9; autotrace ].
Qed.

Lemma trace_spec: forall v w t, v →(t)→* w -> hd 0 t = v /\ last t 0 = w.
Proof.
  intros. induction H. simpl. auto.
  split; simpl. auto.
  destruct t; [inv H0 | now destruct IHtrace].
Qed.

Lemma trace_subpath: forall u v t i j,
  trace u v t -> i <= j < length t -> (nth i t 0 →* nth j t 0).
Proof.
  intros.
  generalize dependent j. generalize dependent i.
  induction H.
  - intros. simpl in *. replace i with 0 by lia. replace j with 0 by lia. autopath. 
  - intros. destruct i; destruct j.
  + simpl. autopath.
  + simpl in *. pose proof (IHtrace 0 j ltac:(lia)). replace (nth 0 t 0) with v in *. autopath.
    apply trace_spec in H0 as [HD]. destruct t; simpl in *; auto.
  + lia.
  + simpl in *. apply IHtrace; lia. 
Qed.

Lemma trace_subpath_start: forall u v t i,
  trace u v t -> i < length t -> (u →* nth i t 0).
Proof.
  intros. enough (u = nth 0 t 0) as N. rewrite N. apply trace_subpath with u v. auto. lia.
  apply trace_spec in H as []. rewrite <- H. destruct t; auto.
Qed.

Lemma trace_subpath_end: forall u v t i,
  trace u v t -> i < length t -> (nth i t 0 →* v).
Proof.
  intros. enough (v = nth (length t - 1) t 0) as N. rewrite N. apply trace_subpath with u v. auto. lia.
  apply trace_spec in H as []. rewrite <- H1. destruct t. auto.
  replace (length (v0::t) - 1) with (length t). apply last_nth. simpl. lia.
Qed.

Lemma trace_hd: forall u v t, (u →(t)→* v) -> exists t', t = u::t'.
Proof.
  intros. copy H. apply trace_spec in H as [H L]. destruct t. inv H0.
  exists t. enough (u=v0) as H1 by (now rewrite H1).
  apply trace_spec in H0; destruct H0; now simpl in H0.
Qed.

Lemma trace_concat: forall u v w t1 t2, (u →(t1)→* v) -> (v →(v::t2)→* w) -> u →(t1++t2)→* w.
Proof.
  intros. induction H. auto.
  apply IHtrace in H0. enow econstructor.
Qed.

Lemma trace_in_inv_full: forall u v t x, (u →(t)→* v) -> In x t -> exists t1 t2, u →(t1)→* x /\ x →(x::t2)→* v /\ t = t1++t2.
Proof.
  intros. induction H.
  * destruct H0; try contradiction. subst. exists (x::nil), nil. split; [|split]; now constructor.
  * intros. destruct H0.
    + subst. exists (x::nil), t. split; [|split]; econstructor; eauto; autopath.
    + apply IHtrace in H0 as [t1 [t2 [? []]]]. exists (u::t1), t2. split; [|split].
      econstructor; eauto. auto. subst. auto.
Qed.

Lemma trace_in_inv: forall u v t x, (u →(t)→* v) -> In x t -> u →* x /\ x →* v.
Proof.
  intros. eapply trace_in_inv_full in H; eauto. destruct H as [t1 [t2 [? []]]].
  split; enow eapply trace_path.
Qed.

Lemma path_right_inv: forall v w,
  v <> w -> v →* w -> exists x, v →* x /\ x → w.
Proof.
  intros. apply path_trace in H0 as [t]. apply trace_right_inv in H0 as [x [? [? []]]].
  * exists x. now split; [apply trace_path in H0 |].
  * destruct H0. contradiction. destruct H1; simpl; lia.
Qed.


(*** POSTDOMINANCE ***)

Section Postdom.

Variable exit: V.
Hypothesis EV: vertex exit.

Definition postdom (v w: V) :=
  vertex v /\ vertex w /\
  forall t, (w →(t)→* exit) -> In v t.

Notation "u →→ v →( t )→* w" := (trace u w (u::t)) (only parsing, at level 9, v at level 8).

Lemma postdom_refl: forall v,
  vertex v -> postdom v v.
Proof.
  intros. unfold postdom; repeat split; auto.
  intros. destruct H0; apply in_eq.
Qed.

Lemma postdom_spec: forall v w,
  vertex v -> vertex w ->
  postdom v w <-> v = w \/ (w <> exit /\ forall w', (w → w') -> postdom v w').
Proof.
  intros v w V W. split; intros.
  + case (Nat.eq_dec v w); intros. auto. right. split.
   - red; intro. rewrite H0 in *. destruct H as [? []]. destruct H2 with (exit::nil). constructor. exact EV. lia. auto.
   - intros w' e. split. now destruct H. split. autopath.
     intros t T. assert (w →→ w' →(t)→* exit) by (constructor 2 with w'; auto).
     apply H in H0. destruct H0. congruence. auto.
  + destruct H.
   - rewrite H. repeat split; auto.
     intros t p. apply trace_hd in p as [p]. rewrite H0. now apply in_eq.
   - repeat split; auto. intros t p. inv p. lia. destruct H as [NE PD]. apply PD in H0. apply H0 in H1. now apply in_cons.
Qed.

Corollary postdom_edge: forall v w p,
  v <> p -> (v → w) -> postdom p v -> postdom p w.
Proof.
  intros. apply postdom_spec in H1 as [|[]]; try congruence; auto; now destruct H1.
Qed.

Lemma postdom_split: forall v w, postdom v w -> (w →* exit) -> (w →* v /\ v →* exit).
Proof.
  intros. apply path_trace in H0 as [t]. apply H in H0 as IN.
  destruct (in_nth nat v 0 t IN) as [n [N L]]. split; rewrite <- N.
  + apply trace_subpath_start with exit; auto.
  + apply trace_subpath_end with w; auto. 
Qed.

Lemma postdom_concat: forall v w u, postdom v w -> postdom w u -> postdom v u.
Proof.
  unfold postdom. intros. destruct H, H0, H1, H2. repeat split; auto.
  intros. copy H5. apply H4 in H5. apply trace_in_inv_full with (x:=w) in H6; auto. decompose [ex and] H6.
  apply H3 in H8. destruct H8. now subst. rewrite H10. enow apply in_app.
Qed.

Lemma postdom_exit_1: forall v, vertex v -> postdom exit v.
Proof.
  intros. repeat split; auto. intros. copy H0. apply trace_spec in H0 as []. rewrite <- H2. apply last_In. now inv H1. 
Qed.

Lemma postdom_exit_2: forall v, postdom v exit -> v = exit.
Proof.
  intros. destruct H, H0. assert (exit →(exit::nil)→* exit) by autotrace. apply H1 in H2 as []. lia. inv H2.
Qed.

End Postdom.


(*** TOPOLOGICAL SORT ***)

Section TopSort.

Definition top_sort (idx: list V) : Prop :=
  Permutation g.(vs) idx /\
  forall u v, (u <<= v in idx) -> ~ (v → u).

Variable idx: list V.
Hypothesis IDX: top_sort idx.

Lemma idx_in: forall x, In x idx <-> vertex x.
Proof.
  intros. destruct IDX. split; intro; unfold vertex in *.
  now apply Permutation_in with (l:=idx).
  now apply Permutation_in with (l:=g.(vs)).
Qed.

Lemma get_idx_in: forall x, vertex x -> {ix: nat | nth_error idx ix = Some x}.
Proof.
  intros. apply idx_in with (x:=x) in H. exact (index_nat idx x H).
Qed.

Lemma top_sort_nodup: NoDup idx.
Proof.
  intros. destruct IDX. apply Permutation_NoDup in H. auto. apply g.(nodup).
Qed.

(*** Some relations between edges and << ***)

Lemma edge_before: forall u v, 
  (u → v) -> u << v in idx.
Proof.
  intros.
  assert (In u idx) by (apply idx_in; auto; autopath).
  assert (In v idx) by (apply idx_in; auto; autopath).
  assert (u <<= u in idx) by now apply (beforeeq_id Nat.eq_dec).
  assert (u <> v). { intro. destruct IDX. pose (H5 u u H2). subst. auto. }
  case (before_dec Nat.eq_dec idx u v H3 H0 H1). auto.
  intro. destruct IDX. apply before_yields_eq in b. pose (H5 v u b). exfalso. now apply n in H.
Qed.

Lemma path_before: forall u v,
  u <> v ->
  (u →* v) -> u << v in idx.
Proof.
  intros. induction H0. contradiction.
  destruct (Nat.eq_dec v w).
  * subst. now apply edge_before.
  * apply IHpath in n. eapply edge_before in H0; eapply before_trans; eauto; now apply top_sort_nodup.
Qed.

Lemma path_beforeeq: forall u v,
  (u →* v) -> u <<= v in idx.
Proof.
  intros. case (Nat.eq_dec u v); intro.
  * subst. apply (beforeeq_id Nat.eq_dec). apply idx_in. now induction H.
  * now apply path_before in H; [apply before_yields_eq|].
Qed.

Lemma edge_neq: forall v w,
  v → w -> v <> w.
Proof.
  intros. apply edge_before, (before_id_neq Nat.eq_dec) in H; auto. apply top_sort_nodup.
Qed.

Lemma before_edge_trans: forall u v w,
  u << v in idx -> v → w -> u << w in idx.
Proof.
  intros. apply edge_before in H0. enow eapply before_trans; try apply top_sort_nodup.
Qed.

Lemma edge_before_trans: forall u v w,
  u → v -> v << w in idx -> u << w in idx.
Proof.
  intros. apply edge_before in H. enow eapply before_trans; try apply top_sort_nodup.
Qed.

Lemma beforeeq_edge_trans: forall u v w,
  u <<= v in idx -> v → w -> u << w in idx.
Proof.
  intros. apply edge_before in H0. apply (beforeeq_split Nat.eq_dec) in H as []. now subst. enow eapply before_trans; try apply top_sort_nodup.
Qed.

Lemma edge_beforeeq_trans: forall u v w,
  u → v -> v <<= w in idx -> u << w in idx.
Proof.
  intros. apply edge_before in H. apply (beforeeq_split Nat.eq_dec) in H0 as []. now subst. enow eapply before_trans; try apply top_sort_nodup.
Qed.

Lemma edge_path_exclusive: forall v w,
  v → w -> ~ w →* v.
Proof.
  intros. intro. apply edge_before in H. apply path_before in H0;
  [now apply before_unique in H; try apply top_sort_nodup | apply (before_id_neq Nat.eq_dec) in H; try lia; apply top_sort_nodup].
Qed.

Lemma edge_edge_exclusive: forall v w,
  v → w -> ~ w → v.
Proof.
  intros. intro. assert (v →* w) by autopath. now apply edge_path_exclusive in H1.
Qed.

End TopSort.

End Graph.


(* Global notation for edges and paths *)
Notation "v → w 'in' g" := (edge g v w) (at level 49).
Notation "v →* w 'in' g" := (path g v w) (at level 49).

Notation "v →( t )→* w 'in' g" := (trace g v w t) (at level 50).

Ltac autopath :=
  match goal with
   | [ |- (?v →* ?v in ?g) ] => constructor; auto; try autopath
   | [ H: ?v → ?w in ?g |- vertex ?g ?w ] => let I := fresh in destruct H as [_ [_ I]]; exact I
   | [ H: ?v → ?w in ?g |- vertex ?g ?v ] => let I := fresh in destruct H as [_ [I _]]; exact I
   | [ H: ?u → ?v in ?g |- ?u →* ?v in ?g ] => constructor 2 with v; [exact H | autopath]
   | [ H1: ?u → ?v in ?g, H2: ?v →* ?w in ?g |- ?u →* ?w in ?g ] => constructor 2 with v; [exact H1 | exact H2]
   | [ H1: ?u →* ?v in ?g, H2: ?v → ?w in ?g |- ?u →* ?w in ?g ] => enow eapply path_right
   | [ H1: ?u →* ?v in ?g, H2: ?v →* ?w in ?g |- ?u →* ?w in ?g ] => enow eapply path_concat
  end.

Ltac autotrace :=
  match goal with
   | [ |- (?v →(?v::nil)→* ?v in ?g) ] => constructor; auto; try autopath
   | [ H: ?u → ?v in ?g |- ?u →(?u::?v::nil)→* ?v in ?g ] => constructor 2 with v; [exact H | autotrace]
   | [ H1: ?u → ?v in ?g, H2: ?v →* ?w in ?g |- ?u →* ?w in ?g ] => constructor 2 with v; [exact H1 | exact H2]
   | [ H1: ?u → ?v in ?g, H2: ?v →(?t)→* ?w in ?g |- ?u →(?u::?t)→* ?w in ?g ] => constructor 2 with v; [exact H1 | exact H2]
   | [ H1: ?u →(?t)→* ?v in ?g, H2: ?v → ?w in ?g |- ?u →(?t ++ ?w::nil)→* ?w in ?g ] => enow eapply trace_right
  end.

#[export] Hint Extern 1 => autopath : core.
#[export] Hint Extern 1 => autotrace : core.


(*** GRAPH INDUCTION ***)

(* Strong induction over a sorted graph. *)
Lemma strong_graph_rect: forall g idx (IDX: top_sort g idx) (P: V -> Type),
  (forall v, vertex g v -> (forall p, p <> v -> p →* v in g -> P p) -> P v) ->
  forall v, vertex g v -> P v.
Proof.
  intros.
  pose proof (index_nat idx v ltac:(enow eapply idx_in)) as [iv].
  generalize dependent v. induction iv using strong_rect. intros.
  pose (predecessors g v) as ps. apply X; auto. intros.
  assert (vertex g p) by (inv H1; auto).
  eapply path_before in H1; eauto.
  apply (before_to_set Nat.eq_dec) in H1 as []; [|enow eapply top_sort_nodup]. destruct x. decompose [and] y.
  assert (iv=n0) by (enow eapply index_same; try eapply top_sort_nodup). subst.
  enow eapply X0.
Qed.

(* Strong induction over a sorted graph. *)
Lemma strong_graph_ind: forall g idx (IDX: top_sort g idx) (P: V -> Prop),
  (forall v, vertex g v -> (forall p, p <> v-> p →* v in g -> P p) -> P v) ->
  forall v, vertex g v -> P v.
Proof.
  intros. enow eapply strong_graph_rect.
Qed.

(* Induction over a sorted graph. *)
Lemma graph_rect: forall g idx (IDX: top_sort g idx) (P: V -> Type),
  (forall v, vertex g v -> (forall p, p → v in g -> P p) -> P v) ->
  forall v, vertex g v -> P v.
Proof.
  intros. eapply strong_graph_rect; eauto.
  intros. apply X; auto. intros. apply X0; auto. enow eapply edge_neq.
Qed.

(* Induction over a sorted graph. *)
Lemma graph_ind: forall g idx (IDX: top_sort g idx) (P: V -> Prop),
  (forall v, vertex g v -> (forall p, p → v in g -> P p) -> P v) ->
  forall v, vertex g v -> P v.
Proof.
  intros. enow eapply graph_rect.
Qed.