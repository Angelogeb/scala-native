(* ############################################################ *)
(*                                                              *)
(*                 Type soundness wrt eval^q                    *)
(*                                                              *)
(* ############################################################ *)

Require Export Arith.EqNat.
Require Export Arith.Le.

Require Export stlc1.


(* ############################################################ *)
(* Definitions                                                  *)
(* ############################################################ *)

(* ### Value typing and well-typed runtime environments ### *)

Inductive wf_env : venv -> tenv -> Prop := 
| wfe_nil : forall n, wf_env (@Def vl nil nil n) (@Def ty nil nil n)
| wfe_cons : forall v t vs ts n,
    val_type (expand_env vs v n) v t ->
    wf_env vs ts ->
    get_inv_idx vs = get_inv_idx ts ->
    wf_env (expand_env vs v n) (expand_env ts t n)

with val_type : venv -> vl -> ty -> Prop :=
| v_bool: forall venv b,
    val_type venv (vbool b) TBool
| v_abs: forall env venv tenv y T1 T2 m retcl,
    wf_env venv tenv ->
    has_type (expand_env (expand_env tenv (TFun T1 m T2 retcl) Second) T1 m) y retcl T2 ->
    val_type env (vabs venv m y retcl) (TFun T1 m T2 retcl).


(* type equivalence: only via reflexivity *)
Inductive stp: venv -> ty -> venv -> ty -> Prop :=
| stp_refl: forall G1 G2 T,
   stp G1 T G2 T.

Global Hint Constructors val_type : core.
Global Hint Constructors wf_env : core.

Global Hint Unfold expand_env : core.

Lemma length_env_incr : forall (X : Type) n m env (x : X),
   n = m ->
   length_env n (expand_env env x m) = 1 + length_env n env.
Proof.
  intros. destruct env; destruct n; inversion H; auto.
Qed.
   
Lemma length_env_same : forall (X : Type) n m env (x : X),
   n <> m ->
   length_env n (expand_env env x m) = length_env n env.
Proof.
  intros. destruct env; destruct n; destruct m.
      contradiction; auto.
      auto.
      auto.
      contradiction; auto.
Qed.

Global Hint Rewrite length_env_incr : core.
Global Hint Rewrite length_env_same : core.
Global Hint Unfold not : core.

Lemma wf_length : forall vs ts,
      wf_env vs ts ->
      length_env First vs = length_env First ts /\ length_env Second vs = length_env Second ts.
Proof.
  intros. induction H; auto.
  destruct IHwf_env as [L R].
  destruct n. 
  (* "First" *) split.
  repeat rewrite length_env_incr; auto.
  repeat rewrite length_env_same; auto.
  unfold not; intros. inversion H2. unfold not; intros. inversion H2.
  (* "Second" *) split.
  repeat rewrite length_env_same; auto.
  unfold not; intros. inversion H2. unfold not; intros. inversion H2.
  repeat rewrite length_env_incr; auto.
Qed.

Global Hint Immediate wf_length : core.



Lemma wf_idx : forall vs ts,
      wf_env vs ts ->
      get_inv_idx vs = get_inv_idx ts.
Proof.
  intros. induction H; auto.
  destruct vs; destruct ts; destruct n; auto.
Qed.

Global Hint Immediate wf_idx : core.


Lemma valtp_extend : forall vs v v1 T n,
                       val_type vs v T ->
                       val_type (expand_env vs v1 n) v T.
Proof. intros. induction H; eauto. Qed.

Lemma index_extend : forall X vs n a (T: X),
                       index n vs = Some T ->
                       index n (a::vs) = Some T.

Proof.
  intros.
  assert (n < length vs). eapply index_max. eauto.
  assert (n <> length vs). lia.
  assert (beq_nat n (length vs) = false) as E. eapply beq_nat_false_iff; eauto.
  unfold index. unfold index in H. rewrite H. rewrite E. reflexivity.
Qed.

Global Hint Immediate index_extend : core.

Lemma lookup_extend : forall X vs x a (T: X) n,
                       lookup x vs = Some T ->
                       lookup x (expand_env vs a n) = Some T.

Proof.
  intros.
  assert (get_idx x < length_env (get_class x) vs). eapply lookup_max. eauto.
  assert (get_idx x <> length_env (get_class x) vs). lia.
  assert (beq_nat (get_idx x) (length_env (get_class x) vs) = false) as E. eapply beq_nat_false_iff; eauto.
  destruct vs.
  destruct n; destruct x; destruct c; simpl in E;
    inversion H; simpl; try rewrite E; auto.
Qed.

Lemma lookup_safe_ex: forall H1 G1 TF x,
             wf_env H1 G1 ->
             lookup x G1 = Some TF ->
             exists v, lookup x H1 = Some v /\ val_type H1 v TF.
Proof. intros. induction H.
  (* "nil"*) inversion H0. destruct x; destruct c; destruct (n <=? i); inversion H1.
  (* "cons"*) destruct vs as [vl1 vl2 vidx]. destruct ts as [tl1 tl2 tidx].
    apply wf_length in H1. destruct H1 as [H1l H1r].
    destruct x; destruct c; inversion H0.
    (* "VFst"*) destruct n; simpl in H0 ; simpl in H2.
      (* "First"*)
        case_eq (beq_nat i (length tl1)).
        (* "hit"*)
          intros E.
          rewrite E in H0. inversion H0. subst t. simpl.
          assert (beq_nat i (length vl1) = true). eauto.
          rewrite H1. eauto.
        (* "miss"*)
          intros E.
          assert (beq_nat i (length vl1) = false). eauto.
          assert (exists v0, lookup (V First i) (@Def vl vl1 vl2 vidx) = Some v0 /\ val_type (@Def vl vl1 vl2 vidx) v0 TF) as HI.
          eapply IHwf_env. simpl. rewrite E in H0. eauto.
          inversion HI as [v0 HI1]. inversion HI1.
          eexists. econstructor. eapply lookup_extend; eauto. eapply valtp_extend; eauto.
    (* "Second"*)
       assert (exists v0, lookup (V First i) (@Def vl vl1 vl2 vidx) = Some v0 /\ val_type (@Def vl vl1 vl2 vidx) v0 TF) as HI.
       eapply IHwf_env. simpl. eauto.
       inversion HI as [v0 HI1]. inversion HI1.
       eexists. econstructor. eapply lookup_extend; eauto. eapply valtp_extend; eauto.
  (* "VSnd"*) destruct n; simpl in H0; simpl in H2.
    (* "First"*)
       assert (exists v0, lookup (V Second i) (@Def vl vl1 vl2 vidx) = Some v0 /\ val_type (@Def vl vl1 vl2 vidx) v0 TF) as HI.
       eapply IHwf_env. simpl. eauto.
       inversion HI as [v0 HI1]. inversion HI1.
       eexists. econstructor. eapply lookup_extend; eauto. eapply valtp_extend; eauto.
    (* "Second"*)
       case_eq (beq_nat i (length tl2)).
        (* "hit"*)
          intro E.
          rewrite E in H0. simpl. destruct (tidx <=? i); inversion H0.
          subst t.
          assert (beq_nat i (length vl2) = true). eauto.
          rewrite H1. inversion H3. subst vidx. destruct (tidx <=? i); eauto. inversion H5.
        (* "miss"*)
          intro E.
          assert (beq_nat i (length vl2) = false). eauto.
          assert (exists v0, lookup (V Second i) (@Def vl vl1 vl2 vidx) = Some v0 /\ val_type (@Def vl vl1 vl2 vidx) v0 TF) as HI.
          eapply IHwf_env. simpl. destruct (tidx <=? i). inversion H0. rewrite E in H0. rewrite H0. rewrite E. auto. auto.
          inversion HI as [v0 HI1]. inversion HI1.
          eexists. econstructor. eapply lookup_extend; eauto. eapply valtp_extend; eauto.
Qed.
  
Inductive res_type: venv -> option vl -> ty -> Prop :=
| not_stuck: forall venv v T,
      val_type venv v T ->
      res_type venv (Some v) T.

Global Hint Constructors res_type : core.
Global Hint Resolve not_stuck : core.


Lemma valtp_widen: forall vf H1 H2 T1 T2,
  val_type H1 vf T1 ->
  stp H1 T1 H2 T2 ->
  val_type H2 vf T2.
Proof.
  intros. inversion H; inversion H0; subst T2; subst; eauto.
Qed.

Lemma invert_abs: forall venv vf vx T1 n T2 retcl,
  val_type venv vf (TFun T1 n T2 retcl) ->
  exists env tenv y T3 T4,
    vf = (vabs env n y retcl) /\
    wf_env env tenv /\
    has_type (expand_env (expand_env tenv (TFun T3 n T4 retcl) Second) T3 n) y retcl T4 /\
    stp venv T1 (expand_env (expand_env env vf Second) vx n) T3 /\
    stp (expand_env (expand_env env vf Second) vx n) T4 venv T2.
Proof.
  intros. inversion H. repeat eexists; repeat eauto.
Qed.


Lemma ext_sanitize_commute : forall {T} n venv (v:T) c,
   expand_env (sanitize_any venv n) v c = sanitize_any (expand_env venv v c) n.
Proof.
  intros. destruct venv. destruct c; simpl; eauto. 
Qed.

Lemma val_type_sanitize_any : forall n venv res T,
  val_type venv res T ->
  val_type (sanitize_any venv n) res T.
Proof.
  intros. inversion H; eauto.
Qed.

Lemma val_type_sanitize : forall env res T n,
  val_type (sanitize_env n env) res T ->
  val_type env res T.
Proof.
  intros. inversion H; eauto.
Qed.

Lemma wf_sanitize_any : forall n venv tenv,
   wf_env venv tenv ->
   wf_env (sanitize_any venv n) (sanitize_any tenv n).
Proof.
  intros. induction H.
  - simpl. eapply wfe_nil.
  - eapply wfe_cons in IHwf_env.
    rewrite <-ext_sanitize_commute. rewrite <-ext_sanitize_commute.
    eauto. eauto. rewrite ext_sanitize_commute.
    eapply val_type_sanitize_any in H. eauto. eauto.
Qed.  

Lemma wf_sanitize : forall n venv tenv,
   wf_env venv tenv ->
   wf_env (sanitize_env n venv) (sanitize_env n tenv).
Proof.
  intros. destruct n; unfold sanitize_env. destruct venv. destruct tenv.
  assert (length sc0 = length sc). apply wf_length in H; destruct H as [L R]; eauto.
  rewrite H0. eapply wf_sanitize_any. eauto.
  eauto.
Qed.
  

Global Hint Immediate wf_sanitize : core.
   

(* ### Theorem 3.5 ### *)
(* if result of STLC 1/2 evaluation is not a timeout, then *)
(* it is not stuck, and well-typed *)

Theorem full_safety : forall k e n tenv venv res T,
  teval k venv e n = Some res -> has_type tenv e n T -> wf_env venv tenv ->
  res_type venv res T.

Proof.
  intros k. induction k.
  (* 0 *)   intros. inversion H.
  (* S n *) intros. destruct e; inversion H; inversion H0. 
  
  - (* "True" *)  eapply not_stuck. eapply v_bool.
  - (* "False" *) eapply not_stuck. eapply v_bool.

  - (* "Var" *)
    subst.
    destruct (lookup_safe_ex (sanitize_env n venv) (sanitize_env n tenv) T v) as [va [I V]]; eauto. 

    rewrite I. eapply not_stuck. eapply val_type_sanitize. eapply V.

  - (* "App" *)
    remember (teval k venv e1 Second) as tf.
    subst T. subst q.
    
    destruct tf as [rf|]; [ | inversion H3].
    assert (res_type venv rf (TFun T1 m T2 retcl)) as HRF. subst. eapply IHk. symmetry. exact Heqtf. eassumption. eassumption.
    inversion HRF as [? vf].

    subst rf. remember vf as rvf. destruct vf; subst rvf. inversion H8.
    assert (c = m). destruct m; destruct c; [ reflexivity | inversion H8 | inversion H8 | reflexivity]. subst c.
    inversion H8; subst.
    (* assert (retcl = n). destruct n; destruct c0; [ reflexivity | inversion H7 | inversion H7 | reflexivity]. subst c0. *)
    remember (teval k venv e2 m) as tx.

    destruct tx as [rx|].
    2: { destruct retcl. inversion H3. destruct n. inversion H10. inversion H3. }
    assert (res_type venv rx T1) as HRX. subst. eapply IHk; eauto.
    inversion HRX as [? vx].

    destruct (invert_abs venv (vabs e m t retcl) vx T1 m T2 retcl) as
        [env1 [tenv1 [y0 [T3 [T4 [EF [WF [HTY [STX STY]]]]]]]]].
    exact H8.
    (* now we know it's a closure, and we have has_type evidence *)

    inversion EF. subst e. subst y0. clear EF.
    subst rx.

    assert (res_type (expand_env (expand_env env1 (vabs env1 m t retcl) Second) vx m) res T4) as HRY.
        (* "HRY" *)
          subst. remember (teval k
          (expand_env (expand_env env1 (vabs env1 m t retcl) Second) vx
             m) t retcl) as tres.
        destruct retcl. subst. eapply IHk; eauto.
        (* wf_env f x *) econstructor. eapply valtp_widen; eauto.
        (* wf_env f   *) econstructor. eapply v_abs; eauto.
          eauto.
          apply wf_idx. assumption.
          apply wf_idx. econstructor. eauto. assumption. apply wf_idx. assumption.
        destruct n. inversion H10.
        subst. eapply IHk; eauto.
        econstructor. eapply valtp_widen; eauto.
        econstructor. eapply v_abs; eauto.
        eauto.
        eapply wf_idx. eassumption.
        eapply wf_idx. econstructor. eauto. eassumption. apply wf_idx. eassumption.

    inversion HRY as [? vy].

    eapply not_stuck. eapply valtp_widen; eauto.
    
  - (* "Abs" *) intros. inversion H. inversion H0.
    eapply not_stuck. eapply v_abs; eauto.
    eauto.
Qed.
