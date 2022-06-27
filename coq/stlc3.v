(* ############################################################ *)
(*                                                              *)
(*        Semantic equivalence of eval^q and eval^q_s           *)
(*                                                              *)
(* ############################################################ *)

Require Export Arith.EqNat.
Require Export Arith.Le.

Require Export stlc1.
Require Export stlc2.


(* ############################################################ *)
(* Definitions                                                  *)
(* ############################################################ *)

(* ### semantic equivalence ### *)

Inductive equiv_val : stack vl_stack -> vl -> vl_stack -> Prop :=
  | equiv_const : forall b st, equiv_val st (vbool b) (vbool_stack b)
  | equiv_abs : forall H1 H2 idx lS i t c1 c2 H fr,
                      get_stack_frame lS i = Some (fr, idx) ->
                      equiv_env lS (Def H1 H2 idx) (H, (fr, idx)) ->
                      equiv_val lS (vabs (Def H1 H2 idx) c1 t c2) (vabs_stack H i c1 t c2)
with equiv_env : stack vl_stack -> venv -> venv_stack -> Prop :=
  | eqv_forall : forall lS H1 H1s H2 H2s H20,
                      Forall2(fun v vs => equiv_val lS v vs) H1 H1s ->
                      Forall2(fun v vs => equiv_val lS v vs) H2 H2s ->
                      equiv_env lS (Def H1 (H2++H20) (length H20)) (H1s, (H2s, length H20)) 
.

(* Since equiv_env uses equiv_val indirectly through Forall2,
   Coq's auto-generated induction principles are not strong enough.
   Hence, we define our own nested induction principle *)

Definition eqv_nested_ind := fun
  (Pv : stack vl_stack -> vl -> vl_stack -> Prop)
  (Pe : stack vl_stack -> venv -> venv_stack -> Prop)
  (fconst : forall (b : bool) (st : stack vl_stack),
       Pv st (vbool b) (vbool_stack b))
  (fabs : forall (H1 H2 : list vl) (idx : nat) (lS : stack vl_stack)
          (i : st_ptr) (t : tm) (c1 c2 : class) (H : heap vl_stack)
          (fr : list vl_stack),
        get_stack_frame lS i = Some (fr, idx) ->
        Pe lS (Def H1 H2 idx) (H, (fr, idx)) ->
        Pv lS (vabs (Def H1 H2 idx) c1 t c2) (vabs_stack H i c1 t c2))
  (fenv : forall (lS : stack vl_stack) (H1 : list vl) 
         (H1s : list vl_stack) (H2 : list vl) (H2s : list vl_stack)
         (H20 : list vl),
       Forall2 (fun (v : vl) (vs : vl_stack) => Pv lS v vs) H1 H1s ->
       Forall2 (fun (v : vl) (vs : vl_stack) => Pv lS v vs) H2 H2s ->
       Pe lS (Def H1 (H2 ++ H20) (length H20)) (H1s, (H2s, length H20)))
=>
  fix F (s : stack vl_stack) (v : vl) (v0 : vl_stack) (e : equiv_val s v v0): Pv s v v0 :=
match e in (equiv_val s0 v1 v2) return (Pv s0 v1 v2) with
| equiv_const x x0 => fconst x x0
| equiv_abs x x0 x1 x2 x3 x4 c1 c2 x6 x7 x8 x9 =>
  fabs x x0 x1 x2 x3 x4 c1 c2 x6 x7 x8 (
         match x9 in (equiv_env s0 v1 v2) return (Pe s0 v1 v2) with
           | eqv_forall x x0 x1 x2 x3 x4 x5 x6 =>
             fenv x x0 x1 x2 x3 x4
                  ((fix G l l' (fa: Forall2 (fun v v' => equiv_val x v v') l l') := match fa in (Forall2 _ l1 l2) return Forall2 _ l1 l2 with
                                | Forall2_nil _ => Forall2_nil _
                                | @Forall2_cons _ _ _ a b x1 x2 r x4 =>
                                  Forall2_cons a b (F x a b r) (G x1 x2 x4)
                              end) x0 x1 x5)
                  ((fix G l l' (fa: Forall2 (fun v v' => equiv_val x v v') l l') := match fa in (Forall2 _ l1 l2) return Forall2 _ l1 l2 with
                                | Forall2_nil _ => Forall2_nil _
                                | @Forall2_cons _ _ _ a b x1 x2 r x4 =>
                                  Forall2_cons a b (F x a b r) (G x1 x2 x4)
                              end) x2 x3 x6)
         end)
end.

(* lift equivalence to timeout and error results *)
Inductive equiv_opt: stack vl_stack -> option (vl) -> option (vl_stack) -> Prop :=
| e_stuck : forall lS, equiv_opt lS None None
| e_val : forall lS v v_stack, equiv_val lS v v_stack -> equiv_opt lS (Some v) ((Some v_stack)).

Inductive equiv_res: stack vl_stack -> option (option vl) -> option (option vl_stack) -> Prop :=
| e_time : forall lS, equiv_res lS None None
| e_res : forall lS v v_stack, equiv_opt lS v v_stack -> equiv_res lS ((Some v)) ((Some v_stack)).


(* ############################################################ *)
(* Proofs                                                       *)
(* ############################################################ *)

Global Hint Constructors equiv_env : core.
Global Hint Constructors equiv_val : core.
Global Hint Constructors equiv_opt : core.
Global Hint Constructors equiv_res : core.

Lemma equiv_length1 : forall H1 H H2 idx fr lS,
   equiv_env lS (@Def vl H1 H2 idx) (H, fr) ->
   length H1 = length H.
Proof.
   intros.
   inversion H0; subst.
   induction H8.
     reflexivity.
     simpl. apply eq_S.
     apply IHForall2; eauto.
Qed. 

Lemma index1_equiv : forall H1 H H2 idx fr' lS x,
   equiv_env lS (Def H1 H2 idx) (H, fr') ->
   equiv_opt lS (index x H1) (index x H).
Proof.
  intros.
  inversion H0; subst.
  induction H8; eauto.
  simpl.
     replace (length l') with (length l).
     destruct (beq_nat x (length l)); eauto.
  assert (length (x0::l) = length (y::l')); eauto.
  eapply equiv_length1; eauto.
Qed.

Lemma forall2_length : forall A B f l1 l2,
   @Forall2 A B f l1 l2 -> length l1 = length l2.
Proof.
   intros.
   induction H; eauto.
     simpl. apply eq_S. apply IHForall2; eauto.
Qed.

Global Hint Immediate forall2_length : core.

Lemma equiv_length2 : forall H l l0 l1 n n0 lS,
  equiv_env lS (@Def vl l l0 n) (H, (l1, n0)) ->
  length l0 = n0 + length l1.
Proof.
  intros. 
  inversion H0; subst.
  induction H11.
     simpl. lia.
     simpl. rewrite <- plus_n_Sm. apply eq_S.
     apply IHForall2; eauto.
Qed.

Lemma equiv_idx : forall H l l0 l1 n n0 lS,
  equiv_env lS (@Def vl l l0 n) (H, (l1, n0)) ->
  n <= length l0.
Proof.
  intros.
  inversion H0; subst.
  induction H2.
    eauto.
    simpl. rewrite app_length. lia.
Qed.

Lemma index2_equiv : forall H l l0 l1 n n0 lS,
  equiv_env lS (Def l l0 n) (H, (l1, n0)) ->
  n = n0 /\ forall i, (n <= i -> equiv_opt lS (index i l0) (index (i - n0) l1)).
Proof.
  intros. 
  inversion H0; subst.
  split.
    - reflexivity.
    - intros. induction H11.
        + simpl. remember (index i H20) as I.
          destruct I; eauto. symmetry in HeqI. eapply index_max in HeqI.
          apply le_not_gt in H1. apply H1 in HeqI. contradiction.
        + simpl. replace (length l') with (length l0).
             case_eq (beq_nat i (length (l0 ++ H20))); intros E.
           * assert (beq_nat (i - length H20) (length l0) = true) as E2.
            { eapply beq_nat_true_iff. eapply equiv_length2 in H0. eapply beq_nat_true_iff in E. 
              rewrite app_length in E. lia. }
              simpl. rewrite E2. eauto.
           * assert (beq_nat (i - length H20) (length l0) = false) as E2.
            { eapply beq_nat_false_iff. eapply equiv_length2 in H0. eapply beq_nat_false_iff in E.
              rewrite app_length in E. lia. }
              simpl. rewrite E2. apply IHForall2; eauto.
           * eapply forall2_length; eauto.
Qed.

Lemma equiv_sanitize : forall H l l0 l1 n n0 lS,
  equiv_env lS (@Def vl l l0 n) (H, (l1, n0)) ->
  equiv_env lS (@Def vl l l0 (n + length l1)) (H, ([], n0 + length l1)).
Proof.
  intros.
  inversion H0; subst.
  replace (length l1) with (length H2).
  replace (length H20 + length H2) with (length (H2 ++ H20)).
  replace (H2 ++ H20) with ([] ++ H2 ++ H20).
  constructor;eauto.
  reflexivity.
  rewrite app_length. lia.
  eauto.
Qed.

Global Hint Unfold get_stack_frame : core.

Lemma stack_extend_val : forall lS v v' fr,
   equiv_val lS v v' ->
   equiv_val (fr::lS) v v'.
Proof.
  intros. 
  eapply (eqv_nested_ind
            (fun lS v v' => equiv_val (fr::lS) v v')
            (fun lS v v' => equiv_env (fr::lS) v v')).

  - intros. constructor.
  - intros. econstructor. destruct i. simpl. eauto. simpl. eauto. simpl in H3.
    assert (beq_nat n (length lS0) = false).
     { apply index_max in H3. apply beq_nat_false_iff. intro contra. subst. eapply lt_irrefl. eauto. }
    rewrite H5. eauto. eauto.
  - intros. constructor; eauto.
  - eauto.
Qed.

Lemma idx_ext : forall X n l1 l2 (x : X), index n l2 = Some x -> index n (l1 ++ l2) = Some x.
Proof.
  intros. induction l1.
  - simpl. eassumption.
  - simpl. inversion IHl1. eapply index_max in H1.
    assert (n =? length (l1 ++ l2) = false). eapply Nat.eqb_neq. lia.
    rewrite H0. reflexivity.
Qed.

Lemma get_sf : forall X x2 x (x1 : stack X) i, get_stack_frame x1 i = Some x -> get_stack_frame (x2 ++ x1) i = Some x.
Proof.
  intros X x2. induction x2; intros.
  + simpl; eauto.
  + unfold get_stack_frame. destruct i. simpl in H. eassumption. unfold get_stack_frame in H.
    eapply idx_ext; eauto.
Qed.

Lemma stack_extend_val_mul : forall v v' lS lS',
   equiv_val lS v v' ->
   equiv_val (lS' ++ lS) v v'.
Proof.
  intros. 
  eapply (eqv_nested_ind
            (fun lS v v' => equiv_val (lS' ++ lS) v v')
            (fun lS v v' => equiv_env (lS' ++ lS) v v')).

  - intros. constructor.
  - intros. econstructor. simpl. eapply get_sf. eassumption. simpl. eauto.
  - intros. constructor; eauto.
  - eauto.
Qed.

Lemma stack_extend_opt_mul : forall v v' lS lS',
   equiv_opt lS v v' ->
   equiv_opt (lS' ++ lS) v v'.
Proof.
  intros. destruct H.
  constructor.
  constructor. eapply stack_extend_val_mul. eassumption.
Qed.

Lemma stack_extend : forall lS env env' fr, 
   equiv_env lS env env' ->
   equiv_env (fr::lS) env env'.
Proof.
  intros. inversion H; subst.
  econstructor.
  - induction H0; econstructor. apply stack_extend_val; eauto. eauto.
  - induction H3; econstructor. apply stack_extend_val; eauto. eauto.
Qed.

Lemma stack_extend_mul : forall lS lS' env env', 
   equiv_env lS env env' ->
   equiv_env (lS' ++ lS) env env'.
Proof.
  intros. inversion H; subst.
  econstructor.
  - induction H0; econstructor. apply stack_extend_val_mul; eauto. eauto.
  - induction H3; econstructor. apply stack_extend_val_mul; eauto. eauto.
Qed.

Lemma lookup2_equiv : forall env H fr lS i,
   equiv_env (fr::lS) env (H, fr) ->
   equiv_opt (fr::lS) (lookup (V Second i) env) (lookup_stack (V Second i) H (fr::lS)).
Proof.
  intros. destruct env. destruct fr. simpl.
  eapply index2_equiv in H0. destruct H0. subst.   
  case_eq (n <=? i); intros E.
  - eapply H1. eapply leb_complete. eauto.
  - eapply e_stuck. 
Qed.

Lemma fc_env_wf: forall H,
  fc_env H -> (Forall (fun v => wf_val First v) H).
Proof.
  intros. induction H0. eauto. eauto. 
Qed.

Lemma equiv_val_fc : forall lS v v_stack fr,
  equiv_val (fr::lS) v v_stack -> wf_val First v_stack -> equiv_val lS v v_stack.
Proof.
  (* idea: if v_stack is first class, it is a bool or a closure without stack frame. *)
  (* it doesn't need a stack frame *)
  intros.
  eapply (eqv_nested_ind
            (fun lS1 v v_stack =>
               lS1 = fr::lS ->
               equiv_val (fr::lS) v v_stack ->
               wf_val First v_stack ->
               equiv_val lS v v_stack)
            (fun lS1 v v_stack =>
               lS1 = fr::lS ->
               equiv_env (fr::lS) v v_stack ->
               fc_env (fst v_stack) -> (fst (snd v_stack)) = [] ->
               equiv_env lS v v_stack)) with (s:=fr::lS);
    intros; try subst lS0.
  - (* "Bool" *)
    constructor.
  - (* "VAbs" *)
    inversion H8. subst. 
    econstructor; eauto.
    inversion H4. subst.
    inversion H7. subst.
    inversion H15. subst.
    eapply H5; eauto.
  - (* "env" *)
    simpl in H7. simpl in H8. subst. eapply fc_env_wf in H7.
    inversion H4. subst. inversion H6. inversion H16. subst. 
    constructor.
    + clear H6.
      induction H12.
      * eauto.
      * inversion H3. inversion H7. subst. 
        constructor. eapply H9; eauto. eauto. 
    + eauto.
  - eauto.
  - eauto.
  - eauto.
  - eauto. 
Qed.

Lemma equiv_val_fc_mul : forall lS lS' v v_stack,
  equiv_val ((lS' ++ lS)) v v_stack -> wf_val First v_stack -> equiv_val lS v v_stack.
Proof.
  (* idea: if v_stack is first class, it is a bool or a closure without stack frame. *)
  (* it doesn't need a stack frame *)
  intros.
  eapply (eqv_nested_ind
            (fun lS1 v v_stack =>
               lS1 = lS' ++ lS ->
               equiv_val (lS' ++ lS) v v_stack ->
               wf_val First v_stack ->
               equiv_val lS v v_stack)
            (fun lS1 v v_stack =>
               lS1 = lS' ++ lS ->
               equiv_env (lS' ++ lS) v v_stack ->
               fc_env (fst v_stack) -> (fst (snd v_stack)) = [] ->
               equiv_env lS v v_stack)) with (s:=lS' ++ lS);
    intros; try subst lS0.
  - (* "Bool" *)
    constructor.
  - (* "VAbs" *)
    inversion H8. subst. 
    econstructor; eauto.
    inversion H4. subst.
    inversion H7. subst.
    inversion H15. subst.
    eapply H5; eauto.
  - (* "env" *)
    simpl in H7. simpl in H8. subst. eapply fc_env_wf in H7.
    inversion H4. subst. inversion H6. inversion H16. subst. 
    constructor.
    + clear H6.
      induction H12.
      * eauto.
      * inversion H3. inversion H7. subst. 
        constructor. eapply H9; eauto. eauto. 
    + eauto.
  - eauto.
  - eauto.
  - eauto.
  - eauto. 
Qed.


Lemma equiv_fc : forall fr lS v v_stack,
  equiv_res (fr::lS) v v_stack -> wf First v_stack -> equiv_res lS v v_stack.
Proof.
  intros.
  inversion H; subst. eauto. constructor.
  inversion H1; subst. eauto. constructor.
  inversion H0. 
  eapply equiv_val_fc; eauto. 
Qed.

Lemma equiv_fc_mul : forall lS' lS v v_stack,
  equiv_res (lS' ++ lS) v v_stack -> wf First v_stack -> equiv_res lS v v_stack.
Proof.
  intros.
  inversion H; subst. eauto. constructor.
  inversion H1; subst. eauto. constructor.
  inversion H0. 
  eapply equiv_val_fc_mul; eauto. 
Qed. 

Definition get_fenv (vs : option (option vl_stack)) :=
  match vs with
  | Some (Some (vabs_stack h _ _ _ _)) => h
  | _ => []
  end.

(* ### Theorem 3.3 ### *)
(* semantic equivalence of STLC 1/2 and STLCs 1.2 *)

Lemma f2 : forall l1 l2 H1 H2,
  Forall2 (fun v vs => equiv_val l2 v vs) H1 H2 ->
  Forall2 (fun v vs => equiv_val (l1 ++ l2) v vs) H1 H2.
Proof.
  intros. induction H.
  + econstructor.
  + econstructor; eauto. eapply stack_extend_val_mul. eassumption.
Qed.

Lemma idx_length : forall X lS' lS (fr : stack_frame X),
  index (length lS) (lS' ++ fr::lS) = Some fr.
Proof.
  intros. induction lS'.
  - simpl. rewrite Nat.eqb_refl. reflexivity.
  - simpl. erewrite app_length.
    assert (length lS =? length lS' + length (fr :: lS) = false).
    apply Nat.eqb_neq. simpl. unfold not. intros. lia.
    rewrite H.
    eassumption.
Qed.

Theorem teval_equiv : forall k n t env v lS lS' fr env_stack v_stack st,
     teval k env t n = v ->
     teval_stack k (length (fr::lS)) (lS' ++ fr::lS) env_stack t n = (v_stack, st) ->
     
     equiv_env (fr::lS) env (env_stack,fr) ->
     fc_env env_stack -> sc_env (lS' ++ fr::lS) ->
     equiv_res st v v_stack.
Proof.
   intro k. induction k.
   (* "k = 0" *) intros. inversion H. inversion H0. econstructor.
   (* "k = S k" *) intros. destruct t;[idtac|idtac|idtac|idtac|idtac].
     
      (* "True" *) simpl in H. simpl in H0. rewrite stack_split_length in H0. inversion H0. subst. repeat constructor. 
      (* "False" *) simpl in H. simpl in H0. rewrite stack_split_length in H0. inversion H0. subst. repeat constructor. 
    
      - (* "Var" *) simpl in H. simpl in H0. rewrite stack_split_length in H0. subst.
        clear H2; clear H3.
        destruct env; destruct v0; destruct n; destruct c; tryfalse_invert; simpl; inversion H0; subst.
        + (* VFst, First *) econstructor. eapply index1_equiv; eauto. eapply stack_extend_mul. eassumption.
        + (* VSnd, First  *) econstructor.
           case_eq ((length sc) <=? i); intros E. 
           (* "i > length l0" *)
               remember (index i sc) as HIV.
               destruct HIV. symmetry in HeqHIV. apply index_max in HeqHIV.
               apply Nat.leb_le in E. lia.
               constructor. 
           (* "i <= length l0" *)
               constructor.
        + (* VFst, Second *) econstructor. eapply index1_equiv; eauto. eapply stack_extend_mul. eassumption.
        + (*VSnd, Second *) econstructor.
               replace (if sc_min <=? i then index i sc else None) with (lookup (V Second i) (@Def vl fc sc sc_min)); eauto.
               replace (let (fr0, off) := fr in if off <=? i then index (i - off) fr0 else None) with
                    (lookup_stack (V Second i) env_stack (fr::lS)) in *; eauto.
               eapply stack_extend_opt_mul.
               eapply lookup2_equiv. eauto.

      - (* "App" *) (* case result Some *)
        subst. simpl. simpl in H0. rewrite stack_split_length in H0.
        
        remember (fr::lS) as lS1.
        
        remember (teval k env t1 Second) as tf.
        remember (teval_stack k (S (length lS)) (lS' ++ lS1) env_stack t1 Second) as tf_stack.
        destruct tf_stack as [tf_stack st'].

        assert (equiv_res st' tf tf_stack) as EF. subst lS1. eapply IHk; eauto.
        destruct EF. inversion H0; subst. econstructor.
        destruct H. inversion H0; subst. econstructor. econstructor.
        inversion H. rewrite <- H6 in H0. inversion H0. econstructor. econstructor.
        eapply sc_env_app_inv in H3. destruct H3.
        rewrite <- H11 in H0.
        assert (Heqst' := Heqtf_stack). symmetry in Heqst'. rewrite HeqlS1 in Heqst'.
        eapply res_stack in Heqst'. destruct Heqst'. destruct H13. clear H14.

        subst lS2. subst lS1. subst lS0. symmetry in Heqtf_stack.
        eapply fc_eval in Heqtf_stack; eauto.
        2: { eapply sc_env_app; eauto. }
        destruct Heqtf_stack.
        
        remember (teval k env t2 c1) as tx.
        remember (teval_stack k (S (length lS)) (x ++ lS' ++ fr :: lS) env_stack t2 c1) as tx_stack.
        destruct tx_stack as [tx_stack st''].
        symmetry in Heqtx_stack. rewrite app_assoc in Heqtx_stack.

        assert (equiv_res st'' tx tx_stack) as EX. eapply IHk with (lS' := x ++ lS'); eauto.
        rewrite <- app_assoc. eassumption.
        destruct EX.
        destruct c2; destruct n; inversion H0; eauto.
        destruct H14.
        destruct c2; destruct n; inversion H0; eauto.
        assert (Heqst'' := Heqtx_stack).
        eapply res_stack in Heqst''. destruct Heqst''. destruct H15.
        apply fc_eval in Heqtx_stack; eauto.
        2: { rewrite <- app_assoc. eassumption. }
        destruct Heqtx_stack.

        rewrite H7 in H0. simpl expand_env_stack in H0. subst lS0.

        destruct c1.
        * (* 1 -> c *) intuition. subst x0. simpl in *.
          change (S (length ((x ++ lS') ++ fr :: lS))) with
            (length ((vabs_stack H6 i First t c2 :: fr0, idx) :: (x ++ lS') ++ fr :: lS))
            in H0.
          remember (((vabs_stack H6 i First t c2 :: fr0, idx) :: (x ++ lS') ++ fr :: lS)) as st''.
          remember (teval_stack k (length st'') st'' (v_stack1 :: H6) t c2) as tres_stack.
          symmetry in Heqtres_stack.
          destruct tres_stack as [tres_stack st'''].
          assert (Heqst''' := Heqtres_stack).
          rewrite Heqst'' in Heqst'''. eapply res_stack with (lS' := []) in Heqst'''.
          destruct Heqst'''. simpl in H15. destruct H15.
          assert (Hwfres_stack := Heqtres_stack).
          rewrite Heqst'' in Hwfres_stack. eapply fc_eval with (lS' := []) in Hwfres_stack.
          destruct Hwfres_stack. subst.
          2: { econstructor. inversion H17. eassumption. subst. inversion H9. inversion H15. eassumption. }
          2: {
            simpl. subst. econstructor. eassumption. econstructor. inversion H9.
            eassumption. eapply sc_frame. 2: { eassumption. } rewrite app_assoc. eassumption. }

          destruct c2.
          (* 1 -> 1 *)
          intuition. subst. simpl in *.
          remember (teval k (Def (v0 :: H4) (vabs (Def H4 H5 idx) First t First :: H5) idx) t First) as tres.
          assert (equiv_res (lS' ++ fr::lS) tres tres_stack).
          eapply equiv_fc_mul with (lS' := x). eapply equiv_fc. rewrite app_assoc.
          eapply IHk with (lS' := []).
          symmetry; eassumption.
          eassumption.
          eapply stack_extend. inversion H8.
          eapply (eqv_forall
            ((x ++ lS') ++ fr :: lS)
            (v0 :: H4)
            (v_stack1 :: H6)
            (vabs (Def H4 (H11 ++ H15) (length H15)) First t First :: H11)
          ).
          econstructor. eassumption.
          rewrite <- app_assoc. eassumption.
          econstructor.
          rewrite <- app_assoc. subst H5. subst idx. eassumption.
          rewrite <- app_assoc. eassumption.
          econstructor. inversion H17. eassumption.
          inversion H9. inversion H15; eassumption.
          simpl. econstructor. eassumption.
          econstructor. inversion H9; eassumption.
          eapply sc_frame. 2: { eassumption.  }
          rewrite app_assoc; eassumption.
          eassumption. eassumption.
          destruct H10. inversion H0. econstructor.
          destruct H10. inversion H0. repeat econstructor.
          inversion H0. subst st. econstructor. econstructor. eassumption.
          (* 1 -> 2 *)
          destruct n. inversion H0; repeat econstructor.
          remember (teval k (Def (v0 :: H4) (vabs (Def H4 H5 idx) First t Second :: H5) idx) t Second) as tres.
          assert (equiv_res (x0 ++ (vabs_stack H6 i First t Second :: fr0, idx) :: (x ++ lS') ++ fr :: lS) tres tres_stack).
          eapply IHk with (lS' := []).
          symmetry; eassumption.
          eassumption.
          eapply stack_extend. inversion H8.
          eapply (eqv_forall
            ((x ++ lS') ++ fr :: lS)
            (v0::H4)
            (v_stack1 :: H6)
            (vabs (Def H4 (H11 ++ H15) (length H15)) First t Second :: H11)
          ).
          econstructor. eassumption.
          rewrite <- app_assoc. eassumption.
          econstructor. subst idx; subst H5; rewrite <- app_assoc; eassumption.
          rewrite <- app_assoc; eassumption.
          econstructor. inversion H17; eassumption.
          inversion H9. inversion H15; eassumption.
          simpl. econstructor.
          eassumption.
          econstructor. inversion H9; inversion H15; eassumption.
          eapply sc_frame. 2: { eassumption. }
          eassumption.
          remember (x0 ++ (vabs_stack H6 i First t Second :: fr0, idx) :: (x ++ lS') ++ fr :: lS) as stt.
          destruct H10. inversion H0. econstructor.
          destruct H10. inversion H0. econstructor. econstructor.
          inversion H0. econstructor. econstructor. subst. eassumption.

        * clear H16.
          change (S (length (x0 ++ (x ++ lS') ++ fr :: lS))) with
          (length ((v_stack1 :: vabs_stack H6 i Second t c2 :: fr0, idx) :: x0 ++ (x ++ lS') ++ fr :: lS)) in H0.
          remember ((v_stack1 :: vabs_stack H6 i Second t c2 :: fr0, idx) :: x0 ++ (x ++ lS') ++ fr :: lS) as st''.
          remember (teval_stack k (length st'') st'' H6 t c2) as tres_stack.
          symmetry in Heqtres_stack.
          destruct tres_stack as [tres_stack st'''].
          assert (Heqst''' := Heqtres_stack).
          rewrite Heqst'' in Heqst'''. eapply res_stack with (lS' := []) in Heqst'''.
          destruct Heqst'''. simpl in H15. destruct H15.
          assert (Hwfres_stack := Heqtres_stack).
          rewrite Heqst'' in Hwfres_stack. eapply fc_eval with (lS' := []) in Hwfres_stack.
          destruct Hwfres_stack. subst.
          2: { subst. inversion H9. inversion H15. eassumption. }
          2: { simpl. subst. econstructor. eassumption. econstructor. inversion H17. eassumption.
               econstructor. inversion H9. eassumption. eapply sc_frame. 2: { eassumption. } eassumption. }

          destruct c2.
          (* 2 -> 1*)
          intuition. subst x1. simpl in *.
          remember (teval k (Def H4 (v0 :: vabs (Def H4 H5 idx) Second t First :: H5) idx) t First) as tres.
          assert (equiv_res (lS' ++ fr::lS) tres tres_stack).
          eapply equiv_fc_mul; eauto; eapply equiv_fc_mul; eauto; eapply equiv_fc; eauto.
          eapply IHk with (lS' := []).
          symmetry; eassumption.
          rewrite <- app_assoc in Heqtres_stack.
          eassumption.
          eapply stack_extend. inversion H8.
          eapply (eqv_forall
            (x0 ++ x ++ lS' ++ fr :: lS)
            H4 H6
            (v0 :: vabs (Def H4 (H11 ++ H15) (length H15)) Second t First :: H11)
          ).
          eapply f2. eassumption.
          econstructor.
          rewrite <- app_assoc in H14. eassumption.
          econstructor.
          eapply stack_extend_val_mul. subst idx. subst H5. eassumption.
          eapply f2. eassumption.
          inversion H9. inversion H15; eassumption.
          simpl. econstructor. rewrite <- app_assoc in H18. eassumption.
          econstructor. inversion H17; eassumption.
          econstructor. inversion H9; eassumption.
          eapply sc_frame. 2: { eassumption. }
          rewrite <- app_assoc in H18; eassumption.

          remember (lS' ++ fr::lS) as st'''.
          destruct H10. inversion H0. econstructor.
          destruct H10. inversion H0. repeat econstructor.
          inversion H0. subst. econstructor. econstructor. eassumption.
          destruct n. inversion H0. repeat econstructor.
          (* 2 -> 2*)
          simpl. remember (teval k (Def H4 (v0 :: vabs (Def H4 H5 idx) Second t Second :: H5) idx) t Second) as tres.
          assert (equiv_res (x1 ++ (v_stack1 :: vabs_stack H6 i Second t Second :: fr0, idx) :: x0 ++ (x ++ lS') ++ fr :: lS) tres tres_stack).
          eapply IHk with (lS' := []).
          symmetry; eassumption.
          eassumption.
          eapply stack_extend. inversion H8.
          eapply (eqv_forall
            (x0 ++ (x ++ lS') ++ fr :: lS)
            H4 H6
            (v0 :: vabs (Def H4 (H11 ++ H15) (length H15)) Second t Second :: H11)).
          eapply f2. rewrite <- app_assoc. eassumption.
          econstructor. eassumption.
          econstructor. eapply stack_extend_val_mul.
          rewrite <- app_assoc. subst H5; subst idx; eassumption.
          eapply f2. rewrite <- app_assoc. eassumption.
          inversion H9. inversion H15; eassumption.
          simpl. econstructor. eassumption.
          econstructor. inversion H17; eassumption.
          econstructor. inversion H9; eassumption.
          eapply sc_frame. 2: { eassumption. } eassumption.
          remember (x1 ++ (v_stack1 :: vabs_stack H6 i Second t Second :: fr0, idx) :: x0 ++ (x ++ lS') ++ fr :: lS) as st'''.
          destruct H10. inversion H0. econstructor.
          destruct H10. inversion H0. repeat econstructor.
          inversion H0. subst. econstructor. econstructor. eassumption.

      - (* "Abs" *)
        subst. simpl in *. rewrite stack_split_length in H0.
        destruct n.
        + destruct fr. destruct env. inversion H0. 
          econstructor. econstructor. simpl.
          remember H1 as HX. clear HeqHX.
          eapply index2_equiv in HX. destruct HX. subst. 
          remember H1 as HX. clear HeqHX.
          eapply equiv_length2 in HX. rewrite HX. 
          eapply equiv_abs. simpl. eauto.
          eapply equiv_sanitize. eauto.
          eapply stack_extend_mul. eassumption.
        + simpl. destruct fr. destruct env. inversion H0. econstructor. econstructor.
          remember H1 as HX. clear HeqHX.
          eapply index2_equiv in HX. destruct HX. subst. 
          eapply equiv_abs. simpl.
          assert (beq_nat (length lS) (length lS) = true) as A. eapply beq_nat_true_iff. eauto.
          eapply idx_length.
          eapply stack_extend_mul. eassumption.
Qed.
