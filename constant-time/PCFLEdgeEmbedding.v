Require Import Axioms Common Coqlib Classical Datatypes.
Require Import AST Memory Registers Maps Values Events Globalenvs Smallstep Op Integers.
Require Import GraphRTL ListsExtra Before.
Require Import Graph GraphDual InfluenceRegion.
Require Import Smallstep Errors.
Require Import Permutation.
Require Import PCFL PCFLBranchMapping.

Section Theorems.

Variable f: function.
Let idx := f.(idx).
Let IDX := f.(IDX).
Let n := f.(n).

Variable u: V -> bool.

Notation "[[ e ]]" := (existT _ e _) (at level 10).
Notation "& x" := (projT1 x) (at level 10).
Notation "?& x" := (projT2 x) (at level 10).

Definition step_data_inv := step_data_inv f u.

Definition step := step_inv_step f u.
Notation "@ i" := (pow step i (step_empty f u)) (at level 30).

Let pcfl := el_graph f u (@n).

Lemma result_vertex: forall v, vertex pcfl v <-> vertex f.(g) v.
Proof.
  unfold pcfl, el_graph, vertex, vs. firstorder.
Qed.
Hint Extern 1 => apply result_vertex : core.

Lemma exit_vertex: forall i, vertex (el_graph f u (@i)) (exit f).
Proof.
  intros. apply result_vertex. now destruct (proj1 (f.(EXIT) f.(exit)) eq_refl).
Qed.

Ltac unfold_step_1 h := unfold step, step_inv_step, pcfl_step; simpl; case (Nat.eq_dec h.(i) f.(GraphRTL.n)) eqn:E1; simpl; auto; try lia.
Ltac unfold_step_2 h := case (Nat.eq_dec h.(i) (f.(GraphRTL.n)-1)) eqn:E2; simpl; auto; try lia. 
Ltac unfold_step h := unfold_step_1 h; try unfold_step_2 h.

Ltac unfold_step_in_1 H h := unfold step, step_inv_step, pcfl_step in H; simpl in H; case (Nat.eq_dec h.(i) f.(GraphRTL.n)) eqn:E1 in H; simpl; simpl in H; auto; try lia.
Ltac unfold_step_in_2 H h := case (Nat.eq_dec h.(i) (f.(GraphRTL.n)-1)) eqn:E2 in H; simpl; simpl in H; auto; try lia. 
Ltac unfold_step_in H h := unfold_step_in_1 H h; try unfold_step_in_2 H h.


Notation "v ▷ w 'in' hm" := (postdom (el_graph f u hm) f.(exit) w v) (at level 100).

(*** FACTS ABOUT THE RESULTING GRAPH ***)

Section GraphFacts.

(* The resulting graph keeps the topological sorting. *)
Lemma top_sort_retained: top_sort pcfl idx.
Proof.
  split; [now destruct IDX | intros].
  destruct (edge_dec pcfl v u0); auto. apply El_graph_edge in e. apply (EI f u (&@n)) in e. 2: now destruct (@n).
  apply (beforeeq_unique Nat.eq_dec) in H; auto. apply top_sort_nodup with (g:=f.(g)); auto.
Qed.

(* The resulting graph keeps the exit. *)
Lemma unique_exit_remains: forall v,
  is_exit f.(g) v <-> is_exit pcfl v.
Proof.
  intro. split; intro.
  * unfold is_exit. split; [destruct H; now apply result_vertex_iff |].
    apply f.(EXIT) in H. rewrite H. apply new_successors_of_exit.
  * destruct H. split; auto.
    destruct (Nat.eq_dec v f.(exit)); [eapply f.(EXIT); eauto |].
    case (u v) eqn:U.
    + apply (new_successors_uniform_length f u) in U; auto.
      unfold pcfl, step, n in H0. unfold PCFLBranchMapping.step in U. rewrite H0 in U. now apply length_zero_iff_nil.
    + eapply (new_successors_tainted f u) in U.
      unfold pcfl, step, n in H0. unfold PCFLBranchMapping.step in U. congruence.
    Unshelve. all: eauto.
Qed.

Lemma unique_exit_pcfl: forall v,
  v = f.(exit) <-> is_exit pcfl v.
Proof.
  intros. now rewrite <- unique_exit_remains, f.(EXIT).
Qed.

Corollary path_to_exit_pcfl:
  forall v, vertex pcfl v ->
  v →* f.(exit) in pcfl.
Proof.
  intros. eapply top_sort_path_to_exit in H as [e [] ]; eauto. 2: eapply top_sort_retained.
  2: { unfold pcfl, el_graph. generalize (nodup f.(g)), El. rewrite f.(VS). unfold vs. rewrite seq_length. intros. apply f.(N). }
  apply unique_exit_pcfl in H. now subst.
Qed.

Lemma less_successors_pcfl: forall v,
  vertex f.(g) v ->
  length (successors pcfl v) <= length (successors f.(g) v).
Proof.
  intros.
  case (Nat.eq_dec v f.(exit)) eqn:?.
  + copy e. apply unique_exit_pcfl in e0 as []. rewrite H1. simpl. lia.
  + unfold pcfl, n, step. case (u v) eqn:?.
    - copy n0. apply new_successors_uniform_length with (u:=u) in n1; auto.
      unfold PCFLBranchMapping.step in n1. lia.
    - eapply new_successors_tainted with (u:=u) (f:=f) in Heqb; eauto.
      unfold PCFLBranchMapping.step in Heqb.
      rewrite Heqb. simpl. destruct (successors f.(g) v) eqn:?; [|simpl; lia].
      exfalso. now apply n0, f.(EXIT).
  Unshelve. all: auto.
Qed.

Lemma has_successors_pcfl: forall v,
  vertex f.(g) v -> v <> f.(exit) ->
  successors pcfl v <> nil.
Proof.
  intros. intro.
  assert (is_exit pcfl v) by easy.
  now apply unique_exit_pcfl in H2.
Qed.

End GraphFacts.

(*** LEMMATA FROM THE PAPER ***)

(* Similar to Lemma B.2, but using D instead of El *)
Lemma relationship_D_El: forall j v w, j < n ->
  In (v, w) (D (&@j)) ->
  In (v, w) (D (&@(S j))) \/ v = b f (&@j) /\ forall x, In (v, x) (El (&@(S j))) -> (x = w \/ In (x, w) (D (&@(S j)))).
Proof.
  intros. remember (@(S j)) as h. rewrite <- pow_succ in Heqh. remember (@j) as h0.
  unfold_step_in_1 Heqh (&h0).
  + copy e. rewrite Heqh0 in e0. unfold step in e0. rewrite pow_i in e0; lia.
  + destruct h eqn:HH. apply projT1_eq in Heqh. simpl in Heqh. unfold_step_in_2 Heqh (&h0).
    - copy e. rewrite Heqh0 in e0. unfold step in e0. rewrite pow_i in e0; try lia. rewrite Heqh0, e0 in H0.
      unfold step in H0. rewrite D_empty_2 in H0. contradiction.
    - case (Nat.eqb v (b f (&h0))) eqn:VB.
    * right. apply Nat.eqb_eq in VB. rewrite VB in *. split; auto. case u in Heqh.
     ++ unfold uniform_step in Heqh. rewrite Heqh. clear Heqh. unfold D, El.
        intros. apply in_app in H1 as [].
      -- apply (b_not_in_El f) in H1. contradiction. pose (I f u (&h0) (?&h0)). lia.
      -- apply list_in_map_inv in H1 as [? [] ]. destruct x1.
         apply list_in_map_inv in H2 as [? [] ]. destruct x1. apply map_extra_id_In in H3.
         assert (vertex f.(g) (b f (&@j))) as BV. { eapply b_vertex; eauto. destruct (@j). enow simpl. unfold step. rewrite pow_i. lia. lia. }
         case (Nat.eq_dec w x0); intro. left. auto. right. unfold_tuples. apply filter_In. split.
         2: { simpl_excl. destruct a, H6. apply proj1_sig_eq in H6. simpl in H6. subst. apply (successors_index f) in H3; auto.
            apply (before_id_neq Nat.eq_dec), not_eq_sym, Nat.eqb_neq in H3. now rewrite H3. exact (idx_nodup f).
           unfold calcT in H6. destruct x2. apply map_extra_id_In in H6. simpl in H5. subst. eapply (successors_in_D_index f) in H6; eauto. 2: enow destruct (@j).
            apply (before_id_neq Nat.eq_dec), not_eq_sym, Nat.eqb_neq in H6. now rewrite H6. exact (idx_nodup f). }
         apply in_app. right. apply in_flat_map. rewrite H5. eapply (map_extra_id_In_rev nat Nat.eq_dec) in H3 as [? [] ]. eexists (x1, x0). split.
         { apply in_map_iff. eexists x2. split. 2: { unfold calcS. eapply H3. } apply pair_equal_spec; split. auto. destruct x2. simpl in H6. subst. apply min_in_nat_element_proof_irr. now simpl. } 
         { rewrite H5. apply in_map. apply filter_In. split. 2: { unfold negb. rewrite H5 in n4. apply Nat.eqb_neq in n4. now rewrite n4. }
           apply in_cons. rewrite (hash_calcT f u (&h0)) at 1. now apply successors_in_spec. }
     ++ unfold tainted_step in Heqh. rewrite Heqh. clear Heqh. unfold D, El.
        intros. apply in_app in H1 as [].
        -- apply (b_not_in_El f) in H1. contradiction. pose (I f u (&h0) (?&h0)). lia.
        -- simpl in H1. destruct H1; try contradiction. unfold_tuples. remember (min_in_nat _ _ _ _). destruct s0. destruct x1. simpl in *.
           assert (vertex f.(g) (b f (&h0))) as BV. { eapply b_vertex; eauto. destruct h0. enow simpl. rewrite Heqh0. unfold step. rewrite pow_i. lia. lia. }
           case (Nat.eq_dec w x0); intro. left. auto. right. apply filter_In. split.
           2: { destruct a. unfold TandS in i0. assert (x1 <> (PCFL.b f (&h0))).
              { copy i0. apply in_app in i1 as []; [unfold calcT in H3 | unfold calcS in H3]; apply map_extra_id_In in H3. eapply (successors_in_D_index f u) in H3; eauto. apply (before_id_neq Nat.eq_dec) in H3; auto; exact (idx_nodup f). now destruct h0. apply (successors_index f) in H3; eauto. apply (before_id_neq Nat.eq_dec) in H3; auto; exact (idx_nodup f). }
              subst. unfold negb. apply Nat.eqb_neq in H3. now rewrite H3. }
           apply in_app. right. rewrite H2 in *. apply in_map. apply filter_In. split. 2: { unfold negb. apply Nat.eqb_neq in n2. now rewrite n2. }
           rewrite hash_TandS. apply in_app. left. now apply successors_in_spec.
    * left. case u in Heqh; [unfold uniform_step in Heqh | unfold tainted_step in Heqh];
      unfold remove_from_b in Heqh; rewrite Heqh; unfold D; apply filter_In; split.
      1,3: apply in_app; now left. 1,2: unfold negb; now rewrite VB.
Qed.


Lemma b_index: forall x bi, (i x) < n -> !(index_nat idx (b f x) bi) = (i x).
Proof.
  intros. unfold b. destruct index_nat. simpl. copy e. rewrite nth_or_error in e; [| now rewrite idx_len with (f:=f)].
  now apply NoDup_nth_error in e; [| now apply idx_nodup with (f:=f) | apply nth_error_len in e0].
Qed.

Lemma relationship_S_D_new_target: forall w j,
  j < n ->
  let b := b f (&@j) in
  In w (successors f.(g) b) ->
  (exists bw, w = (new_target f u) b w bw /\ In (b, w) (El (&@(S j)))) \/
  (exists (w': V) bw, w' = (new_target f u) b w bw /\ In (b, w') (El (&@(S j))) /\ In (w', w) (D (&@(S j)))).
Proof.
  intros.
  rewrite <- pow_succ. remember (@j) as h. unfold_step_1 (&h).
  + copy e. rewrite Heqh in e0. unfold step in e0. rewrite pow_i in e0; lia.
  + destruct h eqn:HH. apply projT1_eq in Heqh. simpl in Heqh. simpl. unfold_step_2 x.
    - unfold b, PCFL.b in H0. simpl in H0. rewrite e in H0. rewrite <- rtl_top_sort_exit in H0; auto.
      pose (proj1 (f.(EXIT) f.(exit)) eq_refl). destruct i. rewrite H2 in H0. contradiction.
    - case u eqn:U.
    * unfold uniform_step, El, D.
      remember (PCFL.uniform_step_obligation_1 _); remember (PCFL.uniform_step_obligation_2 _ _ _ _); remember (PCFL.step_inv_step_obligation_1 _ _ _); remember (PCFL.step_inv_step_obligation_2 _ _ _).
      remember (!(calcS f u _ _ _)) as S. assert (exists W, In W S /\ !W = w) as [W [] ] by (rewrite HeqS; now apply (map_extra_id_In_rev nat Nat.eq_dec)).
      match goal with [ |- (exists _, _ /\ In _ (_ ++ map _ (map ?f S))) \/ _ ] => remember f as fmin end.
      pose (fmin W) as w'2. destruct w'2 as [? w'] eqn:W'.
      unfold w'2 in W'. copy W'. rewrite Heqfmin in W'. rewrite H2 in W' at 1. unfold_tuples.
      destruct (Nat.eq_dec w w').
      ++ left. assert (bw: b → w in f.(g)) by (apply successors_spec; try eapply b_vertex; eauto).
         exists bw. split.
         { unfold new_target, b. simpl. rewrite U. generalize dependent w. rewrite <- H4. intros w ? ? ? weq. rewrite weq. intro. apply min_in_nat_calcT_proof_irr. simpl. now rewrite <- weq at 1.
           assert (PCFL.i x < n) by (rewrite Heqh; unfold step; rewrite pow_i; lia). rewrite b_index; auto. rewrite Heqh; unfold step. now rewrite pow_i; try lia. } 
         { apply in_app. right. simpl. apply in_map_iff. exists (w,w). split; auto. apply in_map_iff. exists W. split; auto. now rewrite <- e, <- H3 in W'0. }
      ++ right. assert (bw: b → w in f.(g)) by (apply successors_spec; try eapply b_vertex; eauto).
         exists w', bw. repeat split.
         { unfold new_target, b. simpl. rewrite U, <- H4. apply min_in_nat_calcT_proof_irr. now simpl.
           assert (PCFL.i x < n) by (rewrite Heqh; unfold step; rewrite pow_i; lia). rewrite b_index; auto. rewrite Heqh; unfold step. now rewrite pow_i; try lia. } 
         { apply in_app. right. simpl. apply in_map_iff. exists (w,w'). split; auto. apply in_map_iff. exists W. split; auto; now rewrite H3. }
         apply filter_In. split.
         { apply in_app; right. apply in_flat_map. exists (w,w'). split. apply in_map_iff. exists W. split; auto; now rewrite H3.
           apply in_map. apply filter_In. split. apply in_eq. unfold negb. apply Nat.eqb_neq in n5. now rewrite n5. }
         unfold negb. destruct (Nat.eq_dec w' (PCFL.b f x)). 2: { apply Nat.eqb_neq in n6. simpl in n6. now rewrite n6. }
         destruct min_in_nat in H4. destruct a. simpl in H4. rewrite <- H4 in *. simpl in i. destruct i; [rewrite H5, HeqS in H1; enow apply inS_not_b in H1 | enow apply inT_not_b in H5].
    * unfold tainted_step, El, D. remember (!(min_in_nat f.(GraphRTL.idx) _ (TandS f u x _ _) _)) as w'.
      pose (I f u x s). destruct (Nat.eq_dec w (!w')).
      ++ left. assert (bw: b → w in f.(g)) by (apply successors_spec; try eapply b_vertex; eauto; simpl in *; lia).
         exists bw. split.
         { unfold new_target, tainted_target, b. simpl. rewrite U. generalize dependent w. intros w ? weq. rewrite weq, Heqw'. intro. apply min_in_nat_TandS_proof_irr. simpl. generalize dependent bw. rewrite <- Heqw', <- weq. intro.
           assert (PCFL.i x < n) by (rewrite Heqh; unfold step; rewrite pow_i; lia). rewrite b_index; auto. rewrite Heqh; unfold step. now rewrite pow_i; try lia. } 
         { apply in_app. right. simpl. rewrite e. auto. }
      ++ right. assert (bw: b → w in f.(g)) by (apply successors_spec; try eapply b_vertex; eauto; simpl in *; lia).
         exists (!w'), bw. repeat split.
         { unfold new_target, tainted_target, b. simpl. rewrite U. rewrite Heqw'. apply min_in_nat_TandS_proof_irr.
           assert (PCFL.i x < n) by (rewrite Heqh; unfold step; rewrite pow_i; lia). rewrite b_index; auto. rewrite Heqh; unfold step. now rewrite pow_i; try lia. }
         { apply in_app. right. simpl. auto. }
         apply filter_In. split. apply in_app; right. apply in_map. apply filter_In. split.
         { rewrite hash_TandS. apply in_app; now right. }
         { unfold negb. apply Nat.eqb_neq in n2. now rewrite n2. }
         { unfold negb. destruct (Nat.eq_dec (!w') b). 2: { apply Nat.eqb_neq in n3. unfold b in n3. simpl in n3. now rewrite n3. }
           destruct min_in_nat in Heqw'. destruct a. copy i. apply inTandS_not_b in i0. unfold b in e. simpl in *. now rewrite <- Heqw', <- e in i0. }
Qed.

(* Lemma B.3, but different proof *)
Theorem postdom_once_in_D: forall j v w, j < n ->
  In (v, w) (D (&@j)) -> v ▷ w in @n.
Proof.
  intros. generalize dependent v. generalize dependent w. pose (n-j) as nj. replace j with (n-nj) by lia. assert (nj <= n) by lia. induction nj.
  * intros. replace (n-0) with n in H1 by lia. unfold step in H1. rewrite D_empty in H1. contradiction.
  * assert (n-nj = S(n-S nj)) as SN by lia.
    intros. copy H1. apply relationship_D_El in H1 as []; try lia.
   - apply IHnj; [lia | now rewrite SN].
   - copy H2. remember (@(n - S nj)) as h. apply (DV f u (&h) (?&h)) in H2 as [].
     destruct H1. apply postdom_spec; auto. apply exit_vertex.
     right. split.
     + destruct (Nat.eq_dec v (exit f)); auto. rewrite e in *. apply (DI f u (&h) (?&h)) in H3.
       exfalso. enow eapply rtl_top_sort_exit_before with (v:=w). 
     + intros. unfold el_graph, vertex, edge, es, step in H6. destruct H6. clear H7.
       apply (idx_in f) in H2 as VI.
       apply El_grows_inv with (j:=n-S nj) (V:=VI) in H6.
       { fold step in H6. apply H5 in H6 as []. rewrite H6. apply postdom_refl; auto. apply exit_vertex. apply IHnj; [lia | now rewrite SN]. }
       { unfold b in H1. rewrite Heqh in H1. unfold step in H1. rewrite pow_i in H1; lia. }
       { unfold b, step in *. revert VI. rewrite H1. intro. rewrite (index_nth Nat.eq_dec). rewrite Heqh, pow_i; try lia. rewrite Heqh, pow_i, (idx_len f) at 1; try lia. exact (idx_nodup f). }
Qed.

(* Each edge's new target is postdominated by its original target (which may be itself) *)
Theorem new_target_spec: forall v w (vw: v → w in f.(g)),
  let w' := (new_target f u) v w vw in v → w' in pcfl /\ (w' ▷ w in (@n)).
Proof.
  intros.
  assert (In v idx) by (eapply idx_in; eauto; now destruct vw as [? [] ]).
  destruct (index_nat idx v H) as [j]. unfold idx in e.
  assert (j < n) by (apply nth_error_len in e; rewrite GraphRTL.top_sort_len with (f:=f) in e; auto).
  assert (S j < n). { exploit edge_before; eauto; intro. destruct (Nat.eq_dec (S j) n); try lia. exploit rtl_top_sort_exit; eauto; intro.
    eapply nth_error_nth in e. replace j with (n-1) in e by lia. unfold n in e. rewrite e in H2. subst. exploit rtl_top_sort_exit_before; eauto. contradiction. }
  apply nth_error_nth with (d:=0) in e.
  remember (@j) as hm.
  assert (b f (&hm) = v) by (rewrite Heqhm; unfold b, step; rewrite pow_i; auto; lia).
  copy vw. apply successors_spec in vw0; try autopath.
  rewrite <- H2, Heqhm in *.
  exploit relationship_S_D_new_target; [eexact H0 | eexact vw0 |]. intros [].
  * destruct H3 as [? [ ] ]. apply El_grows_n in H4; auto.
    replace w' with w in * by (rewrite H3; unfold w'; generalize vw; rewrite <- H2; intro; now replace vw1 with x by apply proof_irr).
    split.
    + now apply El_graph_edge.
    + apply postdom_refl; [ apply exit_vertex | apply result_vertex; now destruct vw as [? [] ] ].
  * destruct H3 as [w'' [bw [TG [ ] ] ] ].
    replace w'' with w' in * by (unfold w'; generalize vw; rewrite TG, <- H2; intro; now replace vw1 with bw by apply proof_irr).
    split.
    + apply El_grows_n in H3; auto. now apply El_graph_edge in H3.
    + now apply postdom_once_in_D in H4.
  Unshelve. exact 0.
Qed.

Corollary edge_embedding: forall v w,
  v → w in f.(g) ->
  v →* w in pcfl.
Proof.
  intros.
  pose proof (new_target_spec v w H).
  remember (new_target _ _ _ _ _) as w'. destruct H0.
  assert (w' →* f.(exit) in pcfl) by enow apply path_to_exit_pcfl.
  apply postdom_split in H1 as []; auto.
Qed.

(* A stronger corollary would be the trace-embedding, similar to the theorem in the paper. *)
Corollary path_embedding: forall v w,
  v →* w in f.(g) ->
  v →* w in pcfl.
Proof.
  induction 1; [| apply edge_embedding in H ]; auto.
Qed.


(* This theorem is similar (but stronger) to Lemma B.5 in the paper, which says that:
   If a vertex v relocates its edge v->w, then v must be non-uni, i.e. in some tainted influence region.
   We make it here a little more precise where the relocated target of such an edge may be. *)
Theorem new_target_chain: forall v w (vw: v → w in f.(g)),
  let w' := new_target f u v w vw in
  w <> w' ->
  chain_inv f u w w'.
Proof.
  intros.
  assert (vertex f.(g) v) by now destruct vw, a.
  assert (In w (successors f.(g) v)) by now apply successors_spec.
  destruct (index_nat idx v ltac:(now apply idx_in)) as [ix].
  assert (b f (&@ix) = v) by now apply b_of_index. 
  rewrite <- H2 in H1. apply relationship_S_D_new_target in H1;
    [ | unfold idx in e; apply nth_error_len in e; now rewrite idx_len in e ].
  decompose [ex and or] H1.
  * subst. irrel_in H3 x vw. lia.
  * subst. irrel_in H6 x0 vw. destruct (@S ix). simpl in *. apply (DT f u x s) in H6. now apply chain_inv_sym.
Qed.

End Theorems.