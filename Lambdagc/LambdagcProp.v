Require Import Metalib.Metatheory.

Require Import Metalib.AssocList.

Require Import Lambdagc.Definitions.

Require Import Coq.Logic.Decidable.

Import LambdagcNotations.





Inductive stuck : program -> Prop := 
  | stuck_proj1_value : forall (H:heap) (x:var),
      (forall (x1 x2:var), ~ binds x (pair (var_f x1) (var_f x2)) H) ->
      stuck (H, proj1 (var_f x))
  | stuck_proj2_value : forall (H:heap) (x:var),
      (forall (x1 x2:var), ~ binds x (pair (var_f x1) (var_f x2)) H) ->
      stuck (H, proj2 (var_f x))
  | stuck_app : forall (H:heap) (x y:var),
      (forall (e1:exp), ~ binds x (abs e1) H) \/ (forall (e2:exp), ~ binds y e2 H) ->
      stuck (H, app (var_f x) (var_f y))
  | stuck_proj1 : forall (H:heap) (e:exp),
    stuck (H, e) ->
    stuck (H, proj1 e)
  | stuck_proj2 : forall (H:heap) (e:exp),
    stuck (H, e) ->
    stuck (H, proj2 e)
  | stuck_app1 : forall (H:heap) (e1 e2:exp),
    stuck (H, e1) ->
    stuck (H, app e1 e2)
  | stuck_app2 : forall (H:heap) (x1:var) (e2:exp),
    stuck (H, e2) ->
    stuck (H, app (var_f x1) e2)
  | stuck_pair1 : forall (H:heap) (e1 e2:exp),
    stuck (H, e1) ->
    stuck (H, pair e1 e2)
  | stuck_pair2 : forall (H:heap) (x1:var) (e2:exp),
    stuck (H, e2) ->
    stuck (H, pair (var_f x1) e2).


(* Theorem not_stuck_can_progress : forall (H:heap) (e:exp), 
  ~(stuck (H,e)) /\ ~(is_answer (H,e)) /\ lc_exp e <->
  exists p', step (H,e) p'.
Proof.
    split.
    - intros hyp. destruct hyp. destruct H1.
      induction e.
      + inversion H2.
      + exfalso. apply H1. simpl. auto.
      + exists ([(fresh (dom_list H), num n)] ++ H, var_f (fresh (dom_list H))).
        apply step_alloc. simpl. auto.
      + exists ([(fresh (dom_list H), abs e)] ++ H, var_f (fresh (dom_list H))).
        apply step_alloc. simpl. auto.
      + inversion H2. destruct e1 eqn:Ee1.
        * inversion H5.
        * destruct e2 eqn:Ee2.
          -- inversion H6.
          -- unfold not in H0. Admitted.
             (* assert((exists e1, get x H = Some (abs e1)) /\ (exists e2, get x0 H = Some e2)).
             { split.  } Admitted. *) *)

Ltac solve_by_inverts n :=
  match goal with | H : ?T |- _ =>
  match type of T with Prop =>
    solve [
      inversion H;
      match n with S (S (?n')) => subst; solve_by_inverts (S n') end ]
  end end.

Theorem stuck_cannot_progress : forall (H:heap) (e:exp),
  lc_exp e ->
  stuck (H,e) \/ is_answer (H,e) ->
  ~(exists p', step (H,e) p').
Proof.
  unfold not. intros H e H_lc H_st C.
  destruct C as [(H', e') H_p'].
  destruct H_st as [H_st | H_ans].
  - generalize dependent H'. generalize dependent e'. 
    induction H_st; subst; intros; inversion H_p'; subst; try (solve_by_inverts 2).
    + apply (H1 x1 x2). assumption.
    + apply (H1 x1 x2). assumption.
    + destruct H1.
      -- apply (H1 e1). assumption.
      -- apply (H1 e2). assumption.
    + apply (IHH_st e'0 H'). assumption.
    + apply (IHH_st e'0 H'). assumption.
    + apply (IHH_st e1' H'). assumption.
    + apply (IHH_st e2' H'). assumption.
    + apply (IHH_st e1' H'). assumption.
    + apply (IHH_st e2' H'). assumption.
  - inversion H_ans; subst. inversion H_p'; subst.
    inversion H7.
Qed.


Theorem not_stuck_implies_progress : forall (H:heap) (e:exp),
  lc_exp e ->
  (~(stuck (H, e)) /\ ~(is_answer (H, e))) ->
  (exists p', step (H,e) p').
Proof.
  unfold not. intros H e H_lc H_st.
  destruct H_st as [H_st H_ans].
  assert (forall (x:var) (E:heap), decidable (exists a, binds x a E)).
  { apply binds_lookup_dec. }
  induction e.
  - inversion H_lc.
  - exfalso. apply H_ans. apply answer_var_f.
  - pick fresh x for (dom H). exists ([(x, num n)] ++ H, var_f x).
    apply step_alloc. auto. apply lc_num. apply heap_num.
  - pick fresh x for (dom H). exists ([(x, abs e)] ++ H, var_f x).
    apply step_alloc. auto. apply H_lc. apply heap_abs.
  - Admitted.
  
  
  (* destruct e1; try (inversion H_lc; destruct IHe1; [ assumption | intros; apply H_st; apply stuck_app1; assumption | intros; inversion H4 |
                      destruct x as [H' e1']; exists (H', app e1' e2); apply step_app1; assumption; assumption]; fail).
    + destruct e2; try(destruct IHe2; [ inversion H_lc; assumption |  intros; apply H_st; apply stuck_app2; assumption | intros; inversion H0 |
                       destruct x0 as [H' e2']; exists ((H', app (var_f x) (e2'))); apply step_app2; apply H0]; fail).
      * destruct (get x H) eqn:E_getx.
        -- destruct e eqn:Ee;
           try (exfalso; apply H_st; apply stuck_app; left; unfold not; intros; rewrite H0 in E_getx; inversion E_getx; fail).
           destruct (get x0 H) eqn:E_getx0.
           ++ pick fresh y for (dom H). exists ([(y, e1)] ++ H, open e0 (var_f y)).
              apply step_app. auto. assumption. assumption. 
           ++ exfalso. apply H_st. apply stuck_app. right. unfold not. intros. rewrite H0 in E_getx0. inversion E_getx0.
        -- exfalso. apply H_st. apply stuck_app. left. unfold not. intros. rewrite H0 in E_getx. inversion E_getx.  
  - destruct e1; try (inversion H_lc; destruct IHe1; [ assumption | intros; apply H_st; apply stuck_pair1; assumption | intros; inversion H4 |
                      destruct x as [H' e1']; exists (H', pair e1' e2); apply step_pair1; assumption; assumption]; fail).
    + destruct e2; try(inversion H_lc; destruct IHe2; [ assumption |  intros; apply H_st; apply stuck_pair2; assumption | intros; inversion H4 |
                       destruct x0 as [H' e2']; exists ((H', pair (var_f x) (e2'))); apply step_pair2; [assumption | assumption]]; fail).
      * pick fresh y for (dom H). exists ([(y, pair (var_f x) (var_f x0))] ++ H, var_f y).
                apply step_alloc. auto.  assumption. apply heap_pair. 
  - destruct e; try(inversion H_lc; destruct IHe; [ assumption | intros; apply H_st; apply stuck_proj1; assumption | intros; inversion H2 |
                    destruct x as [H' e']; exists (H', proj1 e'); apply step_proj1; assumption ]; fail).
    + destruct (get x H) eqn:E_getx.
      * destruct e eqn:Ee;
        try (exfalso; apply H_st; apply stuck_proj1_value; unfold not; intros; rewrite H0 in E_getx; inversion E_getx; fail).
        destruct e0_1; try (exfalso; apply H_st; apply stuck_proj1_value; unfold not; intros; rewrite H0 in E_getx; inversion E_getx; fail).
        destruct e0_2; try (exfalso; apply H_st; apply stuck_proj1_value; unfold not; intros; rewrite H0 in E_getx; inversion E_getx; fail).
        exists (H, var_f x0). apply step_proj1_heap with x1. assumption.
      * exfalso. apply H_st. apply stuck_proj1_value. unfold not. intros. rewrite H0 in E_getx. inversion E_getx.
  - destruct e; try(inversion H_lc; destruct IHe; [ assumption | intros; apply H_st; apply stuck_proj2; assumption | intros; inversion H2 |
                    destruct x as [H' e']; exists (H', proj2 e'); apply step_proj2; assumption ]; fail).
    + destruct (get x H) eqn:E_getx.
    * destruct e eqn:Ee;
      try (exfalso; apply H_st; apply stuck_proj2_value; unfold not; intros; rewrite H0 in E_getx; inversion E_getx; fail).
      destruct e0_1; try (exfalso; apply H_st; apply stuck_proj2_value; unfold not; intros; rewrite H0 in E_getx; inversion E_getx; fail).
      destruct e0_2; try (exfalso; apply H_st; apply stuck_proj2_value; unfold not; intros; rewrite H0 in E_getx; inversion E_getx; fail).
      exists (H, var_f x1). apply step_proj2_heap with x0. assumption.
    * exfalso. apply H_st. apply stuck_proj2_value. unfold not. intros. rewrite H0 in E_getx. inversion E_getx.
Qed. *)

(* Theorem step_deterministic : forall p1 p2 p2',
  step p1 p2 ->
  step p1 p2' ->
  p2 = p2'.
Proof.
  intros p1 p2 p2' H1 H2. generalize dependent p2'. induction H1; intros;
  inversion H2; subst; auto; try solve_by_inverts 3.
  - rewrite H0 in H6. inversion H6. auto.
  - rewrite H0 in H6. inversion H6. auto.
  - rewrite H0 in H8. inversion H8. rewrite H1 in H9.
    inversion H9. auto.
  - apply IHstep in H9. inversion H9. auto.
  - apply IHstep in H7. inversion H7. auto.
  - apply IHstep in H9. inversion H9. auto.
  - apply IHstep in H9. inversion H9. auto.
  - apply IHstep in H6. inversion H6. auto.
  - apply IHstep in H6. inversion H6. auto.
Qed. *)

Example divergent_program :
  step ([(fresh nil, abs (app (var_b 0) (var_b 0)))] ,
       app (var_f (fresh nil)) (var_f (fresh nil)))
       ([(fresh ([fresh nil]), abs (app (var_b 0) (var_b 0)))] ++ [(fresh nil, abs (app (var_b 0) (var_b 0)))] ,
       abs (app (var_b 0) (var_b 0)) ^  (fresh ([fresh nil])) ).
  Proof.
  Admitted.
            
        


