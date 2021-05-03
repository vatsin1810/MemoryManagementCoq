Require Import Metalib.Metatheory.

Require Import Metalib.AssocList.

Require Import Lambdagc.Definitions.

Require Import Coq.Program.Equality.

Import LambdagcNotations.


Inductive fv : program -> program -> Prop :=
  | step_fv : forall (H1 H2:heap) (e:exp),
      AtomSetImpl.Empty (AtomSetImpl.inter (dom H2) (fv_program (H1, e))) ->
      uniq (H1 ++ H2) ->
      fv (H1 ++ H2, e) (H1, e).

Search (?a :: ?b = [?a] ++ ?b ).


Inductive rename : program -> program -> Prop :=
  | step_rename_app : forall (H1 H2:heap) (x y:var) (e xe:exp),
      y `notin` ((dom (H1 ++ H2)) \u fv_heap (H1 ++ [(x, xe)] ++ H2) \u fv_exp e) ->
      (* y `notin` fv_program (H1 ++ [(x, e1)] ++ H2, e2) -> *)
      rename (H1 ++ [(x, xe)] ++ H2, e) (H1 ++ [(y, xe)] ++ H2, subst_exp (var_f y) x e).


Lemma subst_exp_same : forall (x:var) (e:exp),
  subst_exp (var_f x) x e = e.
Proof.
  intros x e. induction e; simpl; auto; try(rewrite IHe; auto); 
  try(rewrite IHe1; rewrite IHe2; auto).
  - destruct (x0 == x). rewrite e. auto. auto.
Qed.

(* Lemma rename_no_effect : forall (H:heap) (e:exp),
  uniq H ->
  rename (H, e) (H, e).
Proof.
  intros H e H_uniq. destruct H as [| x H].
  - apply step_rename_app.
  - destruct x as [x e']. rewrite cons_app_one.
    rewrite <- app_nil_l with (l := [(x, e')] ++ H).
    assert (subst_exp (var_f x) x e = e).
    { apply subst_exp_same. }
    assert (rename (nil ++ [(x, e')] ++ H, e) (nil ++ [(x, e')] ++ H, e) = 
            rename (nil ++ [(x, e')] ++ H, e) (nil ++ [(x, e')] ++ H, subst_exp (var_f x) x e)).
    { rewrite H0. auto. }  unfold heap. 
    rewrite H1. apply step_rename_app. apply uniq_cons_iff in H_uniq.
    destruct H_uniq as [H_uniq H_x]. rewrite app_nil_l. auto.
Qed. *)

Lemma fv_exp_open_exp_wrt_exp_upper :
forall e1 e2,
  fv_exp (open_exp_wrt_exp e1 e2) [<=] fv_exp e2 `union` fv_exp e1.
Proof.
  (* ADMITTED *)
  intros e1 e2.
  unfold open.
  generalize 0.
  induction e1; intro n0; simpl; try (fsetdec).
  - destruct (lt_eq_lt_dec n n0).
    destruct s. simpl. fsetdec.
    fsetdec.
    simpl. fsetdec.
  - rewrite IHe1. fsetdec.
  - rewrite IHe1_1. rewrite IHe1_2.
    fsetdec.
  - rewrite IHe1_1. rewrite IHe1_2.
    fsetdec.
  - rewrite IHe1. fsetdec.
  - rewrite IHe1. fsetdec. 
Qed. (* /ADMITTED *)

Lemma fv_exp_bound_subset : forall (H:heap) (e1:exp),
  (exists x, binds x e1 H) ->
  fv_exp e1 [<=] fv_heap H.
Proof.
  intros H e1 H_bound. destruct H_bound as [x H_bound].
  induction H.
  - inversion H_bound.
  - destruct a as [y e']. apply binds_cons_1 in H_bound. 
    destruct H_bound as [H_x | H_bound].
    + destruct H_x as [H_x H_e1]. rewrite H_e1. simpl.
      fsetdec.
    + apply IHlist in H_bound. simpl. fsetdec.
Qed.

Lemma subst_open : forall (e:exp) (x y:var),
  x `notin` (fv_exp e) ->
  subst_exp (var_f y) x (e ^ x) = e ^ y.
Proof.
  intros e x y H_fv. unfold open. generalize 0.
  induction e; intro n0; simpl; auto; simpl in H_fv.
  - destruct (lt_eq_lt_dec n n0). destruct s; auto.
    + simpl. destruct (x == x). auto. exfalso. apply n1. auto.
    + simpl. auto.
  - destruct (x0 == x). destruct_notin.
    exfalso. apply H_fv. auto. auto.
  - rewrite IHe. auto.  auto.
  - rewrite IHe1. rewrite IHe2. auto.
     fsetdec. fsetdec.
  - rewrite IHe1. rewrite IHe2. auto.
    fsetdec. fsetdec.
  - rewrite IHe. auto. fsetdec.
  - rewrite IHe. auto. fsetdec.
Qed. 


Inductive reorder : program -> program -> Prop :=
  | step_reorder : forall (H1 H2 H3:heap) (e:exp),
      reorder (H1 ++ H2 ++ H3, e) (H2 ++ H1 ++ H3, e).

Lemma fv_heap_app : forall (H1 H2:heap),
  AtomSetImpl.Equal (fv_heap (H1 ++ H2)) (fv_heap H1 \u fv_heap H2).
Proof.
  intros H1 H2. induction H1.
  - simpl. fsetdec.
  - destruct a as (x, e). rewrite <- app_comm_cons. simpl. fsetdec.
Qed.

Lemma heap_increasing : forall (H H':heap) (e e':exp),
  step (H, e) (H', e') ->
  (dom H) [<=] (dom H').
Proof.
  intros H H' e e' H_step.
  generalize dependent H. generalize dependent H'.
  generalize dependent e'. induction e; intros e' H' H H_step; 
  inversion H_step; try (fsetdec); try (rewrite dom_cons; fsetdec).
  - apply IHe1 in H7. auto.
  - apply IHe2 in H2. auto.
  - apply IHe1 in H7. auto.
  - apply IHe2 in H7. auto.
  - apply IHe in H2. auto.
  - apply IHe in H2. auto.
Qed. 


Lemma heap_weakening : forall (H H' H'':heap) (e e':exp),
  step (H, e) (H', e') ->
  AtomSetImpl.Empty (AtomSetImpl.inter (dom H'') (fv_program (H, e))) ->
  step (H ++ H'', e) (H' ++ H'', e').
Proof.
  intros H H' H'' e e' H_step H_dom. remember (H, e) as p.
  remember (H', e') as p'. 
  induction H_step; inversion Heqp; inversion Heqp'; subst.
  - rewrite cons_app_one. rewrite app_assoc. apply step_alloc.
    + rewrite dom_app. simpl in H_dom. fsetdec.
Admitted.


Lemma step_maintains_fv : forall (p p':program),
  step p p' ->
  (fv_program p') [<=] (fv_program p).
Proof.
  intros p p' H_step. induction H_step; 
  try (simpl; simpl in IHH_step; apply heap_increasing in H_step; fsetdec).
  - simpl. fsetdec.
  - simpl. assert (fv_exp (pair (var_f x1) (var_f x2))  [<=] fv_heap H).
    { apply fv_exp_bound_subset. exists x. auto.  } simpl in H1. fsetdec.
  - simpl. assert (fv_exp (pair (var_f x1) (var_f x2))  [<=] fv_heap H).
  { apply fv_exp_bound_subset. exists x. auto.  } simpl in H1. fsetdec.
  - simpl. assert (fv_exp (abs e1) [<=] fv_heap H).
    { apply fv_exp_bound_subset. exists x. auto.  } 
    simpl. assert (fv_exp e2 [<=] fv_heap H).
    { apply fv_exp_bound_subset. exists y. auto.  }
    simpl in H3. unfold open. simpl.
    assert ((fv_exp (open_exp_wrt_exp_rec 0 (var_f z) e1)) [<=] fv_exp (var_f z) `union` fv_exp e1).
    { apply fv_exp_open_exp_wrt_exp_upper. }
    simpl in H5. simpl. fsetdec.
Qed.



(* Lemma postponement : forall (p1 p2 p3:program),
  fv p1 p2 ->
  step p2 p3 ->
  (exists p2' p2'', step p1 p2' /\ fv p2' p2'' /\ rename p2'' p3).
Proof.
  intros p1 p2 p3 H_fv H_step. inversion H_step; inversion H_fv; subst.
  - inversion H10; subst. simpl in H7. pick fresh y for (dom (H ++ H6)).
    exists (([(y, e)] ++ H) ++ H6, var_f y).
    exists ([(y, e)] ++ H, var_f y). split.
    + apply step_alloc. auto. auto. auto.
    + split.
      * apply step_fv. simpl in H7. simpl. fsetdec. solve_uniq.
      * rewrite <- app_nil_l with (l:=[(y, e)] ++ H).
        rewrite <- app_nil_l with (l:=[(x, e)] ++ H).
        assert (subst_exp (var_f x) y (var_f y) = var_f x). { simpl.
        destruct (y == y). auto. exfalso. apply n. auto. }
        rewrite <- H3. apply step_rename_app. rewrite app_nil_l. auto.
  - inversion H8; subst. exists (H ++ H4, var_f x1).
    exists (H, var_f x1). split.
    + apply step_proj1_heap with x2. auto.
    + split.
      * apply step_fv.
        -- simpl. simpl in H5. assert (x1 `in` (fv_heap H)).
           { apply binds_split in H0. destruct H0. destruct H0.
             rewrite H0. rewrite fv_heap_app. rewrite fv_heap_app.
             simpl. fsetdec. } fsetdec.
        -- auto.
      * apply rename_no_effect. solve_uniq.
  - inversion H8; subst. exists (H ++ H4, var_f x2).
    exists (H, var_f x2). split.
    + apply step_proj2_heap with x1. auto.
    + split.
      * apply step_fv.
        -- simpl. simpl in H5. assert (x2 `in` (fv_heap H)).
          { apply binds_split in H0. destruct H0. destruct H0.
           rewrite H0. rewrite fv_heap_app. rewrite fv_heap_app.
           simpl. fsetdec. } fsetdec.
        -- auto.
      * apply rename_no_effect. solve_uniq.
  - inversion H10; subst. pick fresh w for (dom (H ++ H6) \u fv_exp e1).
    exists ([(w, e2)] ++ H ++ H6, e1 ^ w).
    exists ([(w, e2)] ++ H, e1 ^ w). split.
    + apply step_app. auto. auto. auto.
    + split.
      * rewrite <- app_assoc. apply step_fv.
        -- simpl. simpl in H7. rewrite dom_app in Fr.
           assert (fv_exp e2 [<=] fv_heap H).
           { apply fv_exp_bound_subset. exists y. auto. }
           assert (fv_exp (abs e1) [<=] fv_heap H).
           { apply fv_exp_bound_subset. exists x. auto. }
           simpl in H4.
           unfold open.
           assert ((fv_exp (open_exp_wrt_exp_rec 0 (var_f w) e1)) [<=] fv_exp (var_f w) `union` fv_exp e1).
           { apply fv_exp_open_exp_wrt_exp_upper. }
           simpl in H5. fsetdec.
        -- solve_uniq.
      * rewrite <- app_nil_l with (l:=[(w, e2)] ++ H). 
        rewrite <- app_nil_l with (l:=[(z, e2)] ++ H).
        rewrite <- subst_open with (y:=z) (x:=w). apply step_rename_app.
        rewrite app_nil_l. auto. fsetdec.
  - inversion H9; subst. Admitted. *)

Lemma step_closed : forall (p p' : program),
  closed p ->
  step p p' ->
  closed p'.
Proof.
  intros p p' H_closed H_step. 
  induction H_step; unfold closed in *; simpl; simpl in H_closed.
  - fsetdec.
  - assert (x1 `in` (fv_heap H)).
    { apply binds_split in H0. destruct H0. destruct H0.
    rewrite H0. rewrite fv_heap_app. rewrite fv_heap_app.
    simpl. fsetdec. } fsetdec.
  - assert (x2 `in` (fv_heap H)).
    { apply binds_split in H0. destruct H0. destruct H0.
    rewrite H0. rewrite fv_heap_app. rewrite fv_heap_app.
    simpl. fsetdec. } fsetdec.
  - assert (fv_exp e2 [<=] fv_heap H).
    { apply fv_exp_bound_subset. exists y. auto. }
    assert (fv_exp (abs e1) [<=] fv_heap H).
    { apply fv_exp_bound_subset. exists x. auto. }
    simpl in H4.
    unfold open.
    assert ((fv_exp (open_exp_wrt_exp_rec 0 (var_f z) e1)) [<=] fv_exp (var_f z) `union` fv_exp e1).
    { apply fv_exp_open_exp_wrt_exp_upper. }
    simpl in H5. fsetdec.
  - assert (AtomSetImpl.Empty (fv_program (H', e1'))). { apply IHH_step.
    simpl. fsetdec. } simpl in *. assert (dom H [<=] dom H'). 
    { apply heap_increasing with (e:=e1) (e':=e1'). auto. }  fsetdec.
  - assert (AtomSetImpl.Empty (fv_program (H', e2'))). { apply IHH_step.
    simpl. fsetdec. } simpl in *. assert (dom H [<=] dom H'). 
    { apply heap_increasing with (e:=e2) (e':=e2'). auto. }  fsetdec.
  - assert (AtomSetImpl.Empty (fv_program (H', e1'))). { apply IHH_step.
  simpl. fsetdec. } simpl in *. assert (dom H [<=] dom H'). 
  { apply heap_increasing with (e:=e1) (e':=e1'). auto. }  fsetdec.
  - assert (AtomSetImpl.Empty (fv_program (H', e2'))). { apply IHH_step.
  simpl. fsetdec. } simpl in *. assert (dom H [<=] dom H'). 
  { apply heap_increasing with (e:=e2) (e':=e2'). auto. }  fsetdec.
  - assert (AtomSetImpl.Empty (fv_program (H', e'))). { apply IHH_step.
  simpl. fsetdec. } simpl in *. assert (dom H [<=] dom H'). 
  { apply heap_increasing with (e:=e) (e':=e'). auto. }  fsetdec.
  - assert (AtomSetImpl.Empty (fv_program (H', e'))). { apply IHH_step.
  simpl. fsetdec. } simpl in *. assert (dom H [<=] dom H'). 
  { apply heap_increasing with (e:=e) (e':=e'). auto. }  fsetdec.
Qed.

Lemma fv_closed : forall (p p' : program),
  closed p ->
  fv p p' ->
  closed p'.
Proof.
  intros p p' H_closed H_fv. unfold closed in *. inversion H_fv; subst.
  simpl in *. rewrite fv_heap_app in H_closed. rewrite dom_app in H_closed.
  fsetdec.
Qed.

Lemma postponement_ind : forall (H1 H2 Hg:heap) (e1 e2:exp),
  closed (H1 ++ Hg, e1) ->
  fv (H1 ++ Hg, e1) (H1, e1) ->
  step (H1, e1) (H2, e2) ->
  (exists H2' e2', step (H1 ++ Hg, e1) (H2' ++ Hg, e2') /\ fv (H2' ++ Hg, e2') (H2', e2') /\ rename (H2', e2') (H2, e2)).
Proof.
  intros H1 H2 Hg e1 e2 H_closed H_fv H_step.
  generalize dependent H1. generalize dependent H2. 
  generalize dependent e2. 
  induction e1; intros e2 H2 H1 H_closed H_fv H_step; inversion H_fv; subst.
  - inversion H_step; subst. inversion H11.
  - inversion H_step. inversion H12.
  - apply app_inv_head in H; subst. 
    inversion H_step; subst. pick fresh y for (dom (H1 ++ Hg) \u (fv_heap (H1 ++ Hg)) \u (singleton x)). 
    exists ([(y, num n)] ++ H1). exists (var_f y). split.
    + rewrite app_assoc. apply step_alloc. rewrite dom_app in *. 
      rewrite fv_heap_app in *. simpl. fsetdec. auto. auto.
    + split.
      * apply step_fv. simpl. subst. simpl in H6. 
        fsetdec. solve_uniq.
      * rewrite cons_app_one. 
        rewrite <- app_nil_l with (l:=[(y, num n)] ++ H1).
        rewrite <- app_nil_l with (l:=[(x, num n)] ++ H1).
        assert (subst_exp (var_f x) y (var_f y) = var_f x). { simpl.
        destruct (y == y). auto. exfalso. apply n0. auto. }
        rewrite <- H. apply step_rename_app. rewrite app_nil_l.
        rewrite fv_heap_app in *. rewrite dom_app in *.  simpl. fsetdec.
  - admit.
  - apply app_inv_head in H; subst. inversion H_step; subst.
    + inversion H10.
    + admit.
    + destruct (IHe1_1 e1' H2 H1). 
      unfold closed. unfold closed in H_closed. simpl in *. 
      rewrite dom_app in *. rewrite fv_heap_app in *. fsetdec.
      apply step_fv. simpl. simpl in H6. fsetdec. auto. auto.
      destruct H. destruct H. destruct H0. exists x.
      exists (app x0 e1_2). split.
      * apply step_app1. auto. auto.
      * split.
        -- apply step_fv. simpl. simpl in H6.
           inversion H0; subst. apply app_inv_head in H9; subst.
           simpl in H13. apply heap_increasing in H. rewrite dom_app in H.
           rewrite dom_app in H. apply uniq_app_3 in H14. 
           apply uniq_app_3 in H7. unfold disjoint in *.  fsetdec. 
           inversion H0. auto.
        -- inversion H3; subst. rewrite cons_app_one in *. 
           rewrite cons_app_one in *. 
           assert ([x1 ~> var_f y] (app x0 e1_2) = app [x1 ~> var_f y] x0 [x1 ~> var_f y] e1_2).
           { auto. }
           assert (x1 `notin` (fv_exp e1_2)).
           { apply fv_closed in H_fv. apply step_closed in H_step.
             unfold closed in *. simpl in H_step. rewrite cons_app_one in H_step.
             rewrite dom_app in H_step. rewrite dom_app in H_step. 
             rewrite fv_heap_app in H_step. rewrite fv_heap_app in H_step.
             rewrite dom_app in H11. rewrite fv_heap_app in H11. 
             rewrite fv_heap_app in H11. rewrite dom_one in H_step.
             fsetdec. }



  - inversion H_step; subst. apply app_inv_head in H; subst. admit.
  - apply app_inv_head in H; subst. inversion H_step; subst.
    + inversion H10.
    + admit.
    + destruct (IHe1_1 e1' H2 H1).
      * apply step_fv. simpl in H6. simpl. fsetdec. auto.
      * auto.
      * destruct H. destruct H. destruct H0. exists x.
        exists (app x0 e1_2). split.
        -- apply step_app1. auto. auto.
        -- split.
           ++ apply step_fv. inversion H0; subst. 
              apply app_inv_head in H9; subst. simpl in H6.
              simpl in H13. simpl. apply heap_increasing in H.
              apply uniq_app_3 in H14. apply uniq_app_3 in H7.
              rewrite dom_app in H. rewrite dom_app in H. 
              unfold disjoint in *. fsetdec. inversion H0. auto.
           ++ inversion H3; subst.
              ** rewrite cons_app_one in *.  rewrite cons_app_one.
                 assert (app [x1 ~> var_f y] (x0) e1_2 = )
      
  remember (H1, e1) as p1. remember (H2, e2) as p2.
  induction H_step; inversion H_fv; 
  inversion Heqp1; inversion Heqp2; subst.
  - apply app_inv_head in H7; subst. pick fresh y for (dom (H1 ++ Hg)). 
    exists ([(y, e)] ++ H1).
    exists (var_f y).
    split.
    + rewrite app_assoc. apply step_alloc. auto. auto. auto.
    + split.
      * apply step_fv.
        -- simpl. simpl in H10. fsetdec.
        -- solve_uniq.
      * rewrite <- app_nil_l with (l:=[(y, e)] ++ H1).
        rewrite <- app_nil_l with (l:=[(x, e)] ++ H1).
        assert (subst_exp (var_f x) y (var_f y) = var_f x). { simpl.
        destruct (y == y). auto. exfalso. apply n. auto. }
        rewrite <- H. apply step_rename_app. rewrite app_nil_l. auto.
  - apply app_inv_head in H5; subst.
    exists (H2). exists (var_f x1). split.
    + apply step_proj1_heap with x2. auto.
    + split.
      * apply step_fv.
        -- simpl. simpl in H8. assert (x1 `in` (fv_heap H2)).
        { apply binds_split in H0. destruct H0. destruct H.
          rewrite H. rewrite fv_heap_app. rewrite fv_heap_app.
          simpl. fsetdec. } fsetdec.
        -- auto.
      * apply rename_no_effect. solve_uniq.
  - apply app_inv_head in H5; subst.
    exists (H2). exists (var_f x2). split.
    + apply step_proj2_heap with x1. auto.
    + split.
      * apply step_fv.
        -- simpl. simpl in H8. assert (x2 `in` (fv_heap H2)).
        { apply binds_split in H0. destruct H0. destruct H.
          rewrite H. rewrite fv_heap_app. rewrite fv_heap_app.
          simpl. fsetdec. } fsetdec.
        -- auto.
      * apply rename_no_effect. solve_uniq.
  - apply app_inv_head in H7; subst.
    pick fresh w for (dom (H1 ++ Hg) \u fv_exp e0).
    exists ([(w, e3)] ++ H1).
    exists (e0 ^ w). split.
    + rewrite app_assoc. apply step_app. auto. auto. auto.
    + split.
      * apply step_fv.
        -- simpl. simpl in H10. rewrite dom_app in Fr.
          assert (fv_exp e3 [<=] fv_heap H1).
          { apply fv_exp_bound_subset. exists y. auto. }
          assert (fv_exp (abs e0) [<=] fv_heap H1).
          { apply fv_exp_bound_subset. exists x. auto. }
          simpl in H2.
          unfold open.
          assert ((fv_exp (open_exp_wrt_exp_rec 0 (var_f w) e0)) [<=] fv_exp (var_f w) `union` fv_exp e0).
          { apply fv_exp_open_exp_wrt_exp_upper. }
          simpl in H5. fsetdec.
        -- solve_uniq.
      * rewrite <- app_nil_l with (l:=[(w, e3)] ++ H1). 
        rewrite <- app_nil_l with (l:=[(z, e3)] ++ H1).
        rewrite <- subst_open with (y:=z) (x:=w). apply step_rename_app.
        rewrite app_nil_l. auto. fsetdec.
  - apply app_inv_head in H5; subst. simpl in H6. 
    assert (exists p2' p2'' : program, step (H ++ H2, e1) p2' /\ fv p2' p2'' /\ rename p2'' (H', e1')).
    { apply IHH_step. apply step_fv. simpl. fsetdec. auto. }
    destruct H1. destruct H1. destruct H1. destruct H3. destruct x as (H_x, e_x).
    destruct x0 as (H_x', e_x'). exists (H_x, app e_x e2). exists (H_x', app e_x' e2).
    split.
    + apply step_app1. auto. auto.
    + split.
      * inversion H3; subst. apply step_fv.  fsetdec.
  

Lemma diamond : forall (p1 p2 p2':program),
  fv p1 p2 ->
  step p1 p2' ->
  (exists p3, step p2 p3 /\ fv p2' p3).
Proof.
Admitted.



Theorem fv_correctness : forall (p p':program),
  fv p p' ->
  equiv p p' step step.
Proof.
  unfold equiv. intros p p' H_fv n. split.
  - intros H_step. destruct H_step as [x H_step]. 
    destruct H_step as [H H_step]. destruct H_step as [H_step H_num]. 
    generalize dependent p'. remember (var_f x) as e'. 
    remember (H, e') as p_ans. induction H_step.
    + intros p' H_fv. inversion H_fv as [H1 H2 e H_inter H_uniq]; subst. exists x. exists H1. split.
      * inversion H0. auto.
      * inversion H0. subst. simpl in H_inter. 
        apply binds_app_uniq_iff with (x:=x) (a:= (num n)) in H_uniq.
        apply H_uniq in H_num. destruct H_num.
        -- destruct H. auto.
        -- exfalso. destruct H.
            apply binds_dom_contradiction with (x:=x) (a:=(num n)) (E:=H2). 
            auto. fsetdec.
    + intros p' H_fv. apply diamond with (p2' := y) in H_fv. destruct H_fv.
      apply IHH_step with (p' := x1) in Heqp_ans. destruct Heqp_ans. destruct H2.
      destruct H2. destruct H1. exists x2. exists x3. split. eapply multi_step.
      apply H1. auto. auto. destruct H1. auto. auto.
  - intros H_step. destruct H_step as [x H_step]. 
    destruct H_step as [H H_step].
    destruct H_step as [H_step H_num]. 
    generalize dependent p. remember (var_f x) as e'. 
    remember (H, e') as p_ans. induction H_step.
    + intros p H_fv. inversion H_fv as [H1 H2 e H_inter H_uniq]; subst.
      inversion H3; subst. exists x. exists (H ++ H2). split.
      * auto.
      * simpl in H_inter. apply binds_app_iff. left. auto.
    + intros p H_fv. apply postponement with (p3:=y) in H_fv.
      destruct H_fv. destruct H1. apply IHH_step with (p:=x1) in Heqp_ans.
      destruct Heqp_ans. destruct H3. destruct H3. exists x2. exists x3.
      split. eapply multi_step. apply H1. auto. auto. auto. auto.
Qed.
        
