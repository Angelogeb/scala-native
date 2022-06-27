Require Export LibTactics.
Require Export stlc1.
(* ############################################################ *)
(* Definitions and eval^q_s                                     *)
(* ############################################################ *)

(* ### Stacks, stack-frames, closures, etc ### *)

(* To distinguish from the types in stlc1, we frequently use
   a xx_stack suffix:
      - env     ~  env_stack
      - vl      ~  vl_stack
      - lookup  ~  lookup_stack
   we define formal equivalence relations in file stlc3.v *)

Definition stack_frame (X : Type) := prod (list X) nat.
Definition stack (X : Type) := list (stack_frame X).
Definition heap (X : Type) := list X.
Definition env_stack (X : Type) := prod (heap X) (stack_frame X).

(* Stack pointer type.
     - S0 means that there is no stack pointer (fst class closure)
     - Si keeps the index of the stack pointer
*)
Inductive st_ptr : Type :=
| S0 : nat -> st_ptr
| Si : nat -> st_ptr
.

(* STLCs 1/2 values *)
Inductive vl_stack : Type :=
| vbool_stack : bool -> vl_stack
| vabs_stack  : heap vl_stack -> st_ptr -> class -> tm -> class -> vl_stack
.

Definition venv_stack := env_stack vl_stack.

Global Hint Unfold venv_stack : core.

Definition index_heap {X : Type} (n : id) (l : env_stack X) : option X := index n (fst l).
Definition index_stack {X : Type} (n : id) (l : env_stack X) : option X :=
match l with
| (_, ([], _))          => None
| (_, (h, off)) => if off <=? n then index (n - off) h else None
end.

Global Hint Unfold index_heap : core.
Global Hint Unfold index_stack : core.

Section index_examples.
  Let ts_0 := TBool.
  Let ts_1 := TFun TBool First TBool Second.
  Let ts_2 := TFun TBool Second TBool First.
  Let ts_3 := TFun TBool Second TBool Second.
  Let th_0 := TFun TBool First TBool First.
  Let th_1 := TBool.

  Let estack : env_stack ty := ([th_1; th_0], ([ts_3; ts_2; ts_1; ts_0], 2)).

  Example indices_tests :
    index_heap 0 estack = Some th_0 /\
    index_heap 1 estack = Some th_1 /\
    index_stack 0 estack = None /\
    index_stack 1 estack = None /\
    index_stack 2 estack = Some ts_0 /\
    index_stack 3 estack = Some ts_1.
  Proof.
    repeat split.
  Qed.

End index_examples.

Definition lookup_stack {X : Type} (n : var) (h: heap X) (st : stack X) : option X :=
match n with
| V First i => index i h
| V Second i =>
  match st with
  | (fr,off)::_ => if off <=? i then index (i - off) fr else None
  | _ => None
  end
end.

Global Hint Unfold index_heap : core.
Global Hint Unfold index_stack : core.
Global Hint Unfold lookup_stack : core.

Definition expand_env_stack {X : Type} (env : env_stack X) (x : X) (n : class) :=
match env, n with
| (h, (l,off)), First  => (x::h, (l,off))
| (h, (l,off)), Second =>  (h, (x::l, off))
end
.

Definition get_stack_frame {X : Type} (st : stack X) (ptr: st_ptr) :=
  match ptr with
    | S0 idx => Some (nil, idx)
    | Si idx =>  index idx st (*match index idx st with
                     | None => Some (nil,0)
                     | Some s => Some s
                   end *)
end.

(* ### Well-Formedness ### *)

(* well-formedness for `proper` 1st/2nd class values: *)
(* 1st-class closures may not have 2nd class references *)
Inductive wf_val : class -> vl_stack -> Prop :=
| wf_val_const : forall bool c, wf_val c (vbool_stack bool)
| wf_val_closureF : forall tm vheap class idx retcl,
      fc_env vheap ->
      wf_val First (vabs_stack vheap (S0 idx) class tm retcl)
| wf_val_closureS : forall tm vheap class i retcl,
      fc_env vheap ->
      wf_val Second (vabs_stack vheap i class tm retcl)
with fc_env : heap vl_stack -> Prop := (* H, x^1 :v *)
| heap_nil : fc_env []
| heap_cons : forall v vheap,
     wf_val First v ->
     fc_env vheap ->
     fc_env (v::vheap)
with sc_env : stack vl_stack -> Prop :=
| stack_nil : sc_env []
| stack_cons : forall vstack fr idx,
     sc_env vstack ->
     Forall(fun v => wf_val Second v) fr ->
     sc_env ((fr, idx)::vstack).


(* lift wf_val to timeouts and errors *)
Inductive wf : class -> option (option vl_stack) -> Prop :=
| wf_opt : forall v c, wf_val c v -> wf c (Some (Some v))
| wf_timeout: forall c, wf c None
| wf_stuck: forall c, wf c (Some None)
.

Definition fc_val v := wf_val First v.


(* ### Operational Semantics ### *)

(*
None             means timeout
Some None        means stuck
Some (Some v))   means result v
*)

Definition bind_prod {X Y : Type} (vl : option X) (lS : Y) : option (X * Y) :=
  match vl with
  | None => None
  | Some v => Some (v, lS)
  end.

Fixpoint stack_split (st : stack vl_stack) (n : nat) : option (stack vl_stack * stack vl_stack) :=
  match st with
  | [] => None
  | fr::lS =>
    if length st =? n then Some ([], st)
    else match (stack_split lS n) with
    | None => None
    | Some (l1, l2) => Some (fr::l1, l2)
    end
  end.

Definition stack_split_opt (v : option (option (vl_stack * stack vl_stack))) (n : nat) :=
  match v with
  | None => None
  | Some None => Some None
  | Some (Some (v, st)) =>
    match stack_split st n with
    | None => Some None
    | Some (l1, l2) => Some (Some (v, l2))
    end
  end.

(* eval^q_s*)
Fixpoint teval_stack (k : nat) (st_max : nat) (st_over : stack vl_stack)(env: heap vl_stack)(t: tm)(n: class){struct k}: (option (option vl_stack) * stack vl_stack) :=
  match k with
  | 0 => (None, st_over)
  | S k' =>
    match stack_split st_over st_max with
    | None => (Some None, st_over)
    | Some (_, st) =>
      match t, n with
      | ttrue, _ => (Some (Some (vbool_stack true)), st_over)
      | tfalse, _ => (Some (Some (vbool_stack false)), st_over)
      | tvar (V First i),  First  => (Some (lookup_stack (V First i) env st), st_over)
      | tvar (V Second i), First  => (Some None, st_over)
      | tvar i, Second        => (Some (lookup_stack i env st), st_over)
      | tabs m y retcl, First =>
                                    match st with
                                    | [] => (Some None, st_over)
                                    | (fr, idx)::_ => (Some (Some (vabs_stack env (S0 (idx + length fr)) m y retcl)), st_over)
                                    end
      | tabs m y retcl, Second      => match st with
                                      | [] => (Some None, st_over)
                                      | _::st1 => 
                                        (Some (Some (vabs_stack env (Si (length st1)) m y retcl)), st_over)
                                    end
      | tapp ef ex, _   =>
          match teval_stack k' st_max st_over env ef Second, n with
            | (None, _), _ => (None, st_over)
            | (Some None, _), _ => (Some None, st_over)
            | (Some (Some (vbool_stack _)), _), _ => (Some None, st_over)
            | (Some (Some (vabs_stack _ _ _ _ Second)), _), First => (Some None, st_over)
            | (Some (Some (vabs_stack env2 i m ey retcl)), st'), _ =>
              match teval_stack k' st_max st' env ex m with
                | (None, _) => (None, st_over)
                | (Some None, _) => (Some None, st_over)
                | (Some (Some vx), st'') =>
                  match get_stack_frame st' i with
                    | None => (Some None, st_over)
                    | Some fr =>
                      let (env',fr') := expand_env_stack (expand_env_stack (env2,fr) (vabs_stack env2 i m ey retcl) Second) vx m in
                      let frames := fr'::st'' in
                      let (v, st''') := teval_stack k' (length (frames)) frames env' ey retcl in
                      match (v, retcl) with
                      | (Some (Some v), Second) => (Some (Some v), st''')
                      | _ => (v, st_over)
                      end
                  end
              end
        end
      end
    end
  end.


Definition tid := (tabs Second (tvar (V Second 0)) Second).

Definition term := (tapp (tapp tid tid) tid).
Definition ssss : stack vl_stack := ([], 0) :: (@nil (stack_frame vl_stack)).


(* ############################################################ *)
(* Proofs                                                       *)
(* ############################################################ *)

Lemma index_fc: forall H x v,
   fc_env H ->
   index x H = Some v ->
   wf_val First v.
Proof.
   intros H x v Hfc some.
   induction Hfc.
   - inversion some.
   - simpl in some. case_eq (x =? length vheap); intro xlength; rewrite xlength in some.
     + injection some. intro. subst. assumption.
     + apply IHHfc in some. assumption.
Qed.

Lemma lookup_snd : forall H lS x v,
   fc_env H -> sc_env lS ->
   lookup_stack x H lS = Some v ->
   wf_val Second v.
Proof.
   intros.
   destruct v.
   destruct x; destruct c; try solve inversion.
   constructor. constructor.
   destruct x. destruct c1. try solve inversion.
   constructor. assert (wf_val First (vabs_stack h s c t c0)). eapply index_fc. exact H0. exact H2.
   inversion H3; eauto.
   induction H1.
      - inversion H2. 
      - case_eq (idx <=? i); intros E; simpl in H2.
        + rewrite E in H2. induction H3. inversion H2. 
        case_eq ((i - idx) =? (length l)); intros E2; simpl in H2.
          * rewrite E2 in H2. inversion H2; subst; eauto. 
          * rewrite E2 in H2. apply IHForall. simpl. eauto.
        + rewrite E in H2. inversion H2.
Qed.

Lemma subcl_wf : forall v c1 c2,
  subcl c1 c2 = true ->
  wf c1 v -> wf c2 v.
Proof.
  intros.
  destruct c1; destruct c2; tryfalse_invert; eauto.
  repeat (destruct v as [v|]; repeat constructor).
  inversion H0; subst.
  inversion H3; eauto.
Qed.

Lemma sc_frame : forall fr idx lS i,
  sc_env lS ->
  get_stack_frame lS i = Some (fr, idx) ->
  Forall(fun v => wf_val Second v) fr.
Proof.
  intros fr idx lS i H.
  generalize dependent fr. generalize dependent i.
  induction H; intros.
  - destruct i; inversion H. constructor.
  - destruct i; inversion H1; subst.
     + constructor.
     + case_eq (beq_nat n (length vstack)); intros E.
       * rewrite E in H3. inversion H3; subst. assumption.
       * rewrite E in H3. apply IHsc_env with (i := Si n). simpl. assumption.
Qed.

Lemma append_not_nil : forall {X} (x : list X) (fr : X) (lS : list X),
 exists hd tail, (x ++ fr::lS) = hd::tail.
Proof.
  intros. destruct x.
  - simpl. exists fr. exists lS. reflexivity.
  - simpl. exists x. exists (x0 ++ fr :: lS). reflexivity.
Qed.

Lemma sc_env_app : forall l1 l2, sc_env l1 -> sc_env l2 -> sc_env (l1 ++ l2).
Proof.
  intros l1. induction l1; intros.
  + simpl. eassumption.
  + simpl. destruct a. inversion H. econstructor. eapply IHl1. all: eauto.
Qed.

Lemma sc_env_app_inv : forall l1 l2, sc_env (l1 ++ l2) -> sc_env l1 /\ sc_env (l2).
Proof.
  intros l1. induction l1; intros.
  + simpl in H. split. constructor. eassumption.
  + inversion H; subst. eapply IHl1 in H2. destruct H2.
    split; try eassumption. constructor; eauto.
Qed.

Lemma stack_split_length :
  forall x fr lS,
  stack_split (x ++ fr::lS) (length (fr::lS)) = Some (x, fr::lS).
Proof.
  intros. induction x.
  + simpl. erewrite Nat.eqb_refl. reflexivity.
  + simpl. simpl length in IHx. erewrite IHx. erewrite app_length. simpl.
    assert (length x + S (length lS) =? length lS = false).
    erewrite Nat.eqb_neq. lia. erewrite H. reflexivity.
Qed.

Definition with_st (res : option (option (vl_stack * stack vl_stack))) (st : stack vl_stack) :=
  match res with
  | None => None
  | Some None => Some None
  | Some (Some (v, s)) => Some (Some (v, st))
  end.

Definition mts := (@nil (stack_frame vl_stack)).

Lemma res_stack_none : forall k fr lS lS' env_stack t c st,
  teval_stack k (length (fr::lS)) (lS' ++ fr::lS) env_stack t c = (None, st) ->
  st = (lS' ++ fr::lS).
Proof.
  intro k. induction k.
  (* k = 0 *) intros. simpl in H. inversion H. reflexivity.
  (* k = 1 *) intros; destruct t; simpl in H; rewrite stack_split_length in H; try inversion H.
  - destruct v; destruct c0; destruct c; inversion H.
  - remember (teval_stack k (S (length lS)) (lS' ++ fr :: lS) env_stack0 t1 Second) as tf.
    destruct tf. destruct o.
    2: { inversion H. reflexivity. }
    destruct o.
    2: { inversion H. }
    destruct v. inversion H.
    remember (teval_stack k (S (length lS)) s env_stack0 t2 c0) as tx.
    destruct tx. destruct o.
    2: { destruct c1; destruct c; inversion H; reflexivity. }
    destruct o.
    2: { destruct c1; destruct c; inversion H. }
    remember (get_stack_frame s s0) as frame.
    destruct frame.
    2: { destruct c1; destruct c; inversion H.  }
    destruct p. clear H1.
    remember (expand_env_stack (h, (vabs_stack h s0 c0 t c1 :: l, n)) v c0) as estk.
    destruct estk.
    change (S (length s1)) with (length (p::s1)) in H.
    remember (teval_stack k (length (p::s1)) (p :: s1) l0 t c1) as tres.
    destruct tres. destruct o.
    2: { destruct c1; destruct c; inversion H; reflexivity. }
    destruct o.
    destruct c1; destruct c; inversion H.
    destruct c1; destruct c; inversion H.
  - destruct c; destruct fr; inversion H1.
Qed.


Lemma res_stack_some_none : forall k fr lS lS' env_stack t c st,
  teval_stack k (length (fr::lS)) (lS' ++ fr::lS) env_stack t c = (Some None, st) ->
  st = (lS' ++ fr::lS).
Proof.
  intro k. induction k.
  (* k = 0 *) intros. simpl in H. inversion H.
  (* k = 1 *) intros; destruct t; simpl in H; rewrite stack_split_length in H; try inversion H.
  - destruct v; destruct c0; destruct c; inversion H; reflexivity.
  - remember (teval_stack k (S (length lS)) (lS' ++ fr :: lS) env_stack0 t1 Second) as tf.
    destruct tf. destruct o.
    2: { inversion H. }
    destruct o.
    2: { inversion H; reflexivity. }
    destruct v. inversion H. reflexivity.
    remember (teval_stack k (S (length lS)) s env_stack0 t2 c0) as tx.
    destruct tx. destruct o.
    2: { destruct c1; destruct c; inversion H; reflexivity. }
    destruct o.
    2: { destruct c1; destruct c; inversion H; reflexivity. }
    remember (get_stack_frame s s0) as frame.
    destruct frame.
    2: { destruct c1; destruct c; inversion H; reflexivity. }
    destruct p. clear H1.
    remember (expand_env_stack (h, (vabs_stack h s0 c0 t c1 :: l, n)) v c0) as estk.
    destruct estk.
    change (S (length s1)) with (length (p::s1)) in H.
    remember (teval_stack k (length (p::s1)) (p :: s1) l0 t c1) as tres.
    destruct tres. destruct o.
    2: { destruct c1; destruct c; inversion H; reflexivity. }
    destruct o.
    destruct c1; destruct c; inversion H; reflexivity.
    destruct c1; destruct c; inversion H; reflexivity.
  - destruct c; destruct fr; inversion H1.
Qed.

Lemma res_stack : forall k fr lS lS' env_stack t v_stack c st,
  teval_stack k (length (fr::lS)) (lS' ++ fr::lS) env_stack t c = (v_stack, st) ->
  (exists l, st = l ++ lS' ++ fr::lS /\ (c = First -> l = [])).
Proof.
  intros k. induction k.
  (* k = 0 *) intros. simpl in H. inversion H. exists (@nil (stack_frame vl_stack)).
  simpl. repeat split.
  (* k = S k' *)
  intros. destruct t; simpl in H; rewrite stack_split_length in H.
  - inversion H. exists (@nil (stack_frame vl_stack)). repeat split.
  - inversion H. exists (@nil (stack_frame vl_stack)). repeat split.
  - destruct v. destruct c0; destruct c; inversion H; subst; exists (@nil (stack_frame vl_stack));
    repeat split.
  - remember (teval_stack k (S (length lS)) (lS' ++ fr :: lS) env_stack0 t1 Second) as tf.
    destruct tf. destruct o.
    2: { inversion H. exists (@nil (stack_frame vl_stack)). repeat split. }
    destruct o.
    2: { inversion H. exists (@nil (stack_frame vl_stack)). repeat split. }
    destruct v.
    inversion H. exists (@nil (stack_frame vl_stack)). repeat split.
    remember (teval_stack k (S (length lS)) s env_stack0 t2 c0) as tx.
    destruct tx.
    destruct o.
    2: { destruct c1; destruct c; inversion H; exists (@nil (stack_frame vl_stack)); repeat split. }
    destruct o.
    2: { destruct c1; destruct c; inversion H; exists (@nil (stack_frame vl_stack)); repeat split. }
    remember (get_stack_frame s s0) as frame.
    destruct frame.
    2: { destruct c1; destruct c; inversion H; exists (@nil (stack_frame vl_stack)); repeat split. }
    destruct p.
    remember (expand_env_stack (h, (vabs_stack h s0 c0 t c1 :: l, n)) v c0) as stk.
    destruct stk.
    change (S (length s1)) with (length (p::s1)) in H.
    remember (teval_stack k (length (p :: s1)) (p :: s1) l0 t c1) as tres.
    destruct tres.
    destruct o.
    2: { destruct c1; destruct c; inversion H; exists (@nil (stack_frame vl_stack)); repeat split. }
    destruct o.
    2: { destruct c1; destruct c; inversion H; exists (@nil (stack_frame vl_stack)); repeat split. }
    destruct c1; destruct c; inversion H.
    exists (@nil (stack_frame vl_stack)); repeat split.
    exists (@nil (stack_frame vl_stack)); repeat split.
    exists (@nil (stack_frame vl_stack)); repeat split.
    symmetry in Heqtf. eapply IHk in Heqtf. destruct Heqtf. destruct H0. clear H3.
    symmetry in Heqtx. subst s. rewrite app_assoc in Heqtx. eapply IHk in Heqtx.
    destruct Heqtx. destruct H0. subst s1.
    symmetry in Heqtres. rewrite <- app_assoc in Heqtres.
    eapply IHk with (lS' := []) in Heqtres.
    destruct Heqtres. simpl in H0. destruct H0. clear H4. subst st. subst s2.
    exists (x1 ++ p :: x0 ++ x).
    rewrite app_assoc. rewrite app_comm_cons. rewrite app_assoc. repeat split.
    intros. inversion H0.
  - destruct c; destruct fr; inversion H; exists (@nil (stack_frame vl_stack)); repeat split.
Qed.

Theorem fc_eval : forall k fr lS lS' env_stack t v_stack c st,
  teval_stack k (length (fr::lS)) (lS' ++ fr::lS) env_stack t c = (v_stack, st) ->
  fc_env env_stack -> sc_env (lS' ++ fr::lS) ->
  wf c v_stack /\ sc_env st.
Proof.
  intros k.
  destruct v_stack as [v_stack|];[destruct v_stack as [v_stack|]|].
  2: { intros. split. repeat constructor. eapply res_stack_some_none in H. subst st. eassumption. }
  2: { intros. split. constructor. eapply res_stack_none in H. subst. eassumption. }
  generalize dependent fr. generalize dependent lS. generalize dependent lS'.
  generalize dependent t. generalize dependent env_stack0. generalize dependent v_stack.
  induction k; intros.
  (* k = 0 *) inversion H.
  (* k = S k' *) destruct t; simpl in H; rewrite stack_split_length in H; inversion H; clear H3.
  - repeat split; eauto; repeat constructor.
  - repeat split; eauto; repeat constructor.
  - destruct v; destruct c0; destruct c; tryfalse_invert.
    * inversion H; split; eauto. rewrite H3. econstructor. eapply index_fc; eauto.
    * remember (lookup_stack (V First i) env_stack0 (fr :: lS)). injection H; intros. 
      split; [|subst; eauto]. subst o. constructor.
      eapply sc_env_app_inv in H1. destruct H1.
      apply (lookup_snd env_stack0 (fr::lS) (V First i) v_stack); eauto.
    * remember (lookup_stack (V Second i) env_stack0 (fr :: lS)). injection H; intros.
      split; [|subst; eauto]. subst o. constructor.
      eapply sc_env_app_inv in H1. destruct H1.
      apply (lookup_snd env_stack0 (fr::lS) (V Second i) v_stack); eauto.
  - remember (teval_stack k (S (length lS)) (lS' ++ fr :: lS) env_stack0 t1 Second) as tf.
    destruct tf. destruct o; tryfalse_invert. destruct o; tryfalse_invert.
    destruct v; tryfalse_invert.
    symmetry in Heqtf.
    assert (stkf := Heqtf). eapply res_stack in stkf. destruct stkf as [l [eqsf _]].
    assert (wfstkf := Heqtf). eapply IHk in wfstkf; eauto. destruct wfstkf.

    assert (subcl c1 c = true) as Hsub. 1: {
      destruct c1; destruct c; tryfalse_invert; try reflexivity.
    }

    remember (teval_stack k (S (length lS)) s env_stack0 t2 c0) as tx.
    destruct tx; destruct o.
    2: { destruct c1; destruct c; tryfalse_invert. }
    destruct o.
    2: { destruct c1; destruct c; tryfalse_invert. }
    remember (get_stack_frame s s0) as frame. destruct frame.
    2: { destruct c1; destruct c; tryfalse_invert. }
    destruct p; simpl in H.
    symmetry in Heqtx.
    assert (stkx := Heqtx). rewrite eqsf in stkx.
      rewrite app_assoc in stkx. eapply res_stack in stkx. destruct stkx as [l2 [eqsx Hmt]].
    assert (wfstkx := Heqtx). rewrite eqsf in wfstkx. rewrite app_assoc in wfstkx.
    eapply IHk in wfstkx; eauto. destruct wfstkx.
    2: { rewrite eqsf in H3. rewrite <- app_assoc. eassumption. }

    destruct c0.
    * change (S (length s1)) with (length ((vabs_stack h s0 First t c1 :: l0, n) :: s1)) in H.
      remember (teval_stack k
      (length ((vabs_stack h s0 First t c1 :: l0, n) :: s1))
      ((vabs_stack h s0 First t c1 :: l0, n) :: s1) 
      (v :: h) t c1) as tres.
      destruct tres.
      destruct o.
      2: { destruct c1; destruct c; tryfalse_invert. }
      destruct o.
      2: { destruct c1; destruct c; tryfalse_invert. }

      destruct c1; destruct c; inversion H; try (split; eauto); subst v0.

      eapply IHk with (lS' := []). simpl app.
      symmetry; eassumption. econstructor. inversion H4; eassumption.
      inversion H2. inversion H9; eassumption.
      simpl. econstructor. eassumption. econstructor. inversion H2; eassumption.
      eapply sc_frame. 2: { symmetry; eassumption. }
      eassumption.

      eapply subcl_wf; eauto.
      eapply IHk with (lS' := []). simpl app.
      symmetry; eassumption. econstructor. inversion H4; eassumption.
      inversion H2. inversion H9; eassumption.
      simpl. econstructor. eassumption. econstructor. inversion H2; eassumption.
      eapply sc_frame. 2: { symmetry; eassumption. }
      eassumption.

      eapply IHk with (lS' := []). simpl app.
      symmetry; eassumption. econstructor. inversion H4; eassumption.
      inversion H2; inversion H9; eassumption.
      simpl. econstructor. eassumption. econstructor. inversion H2; eassumption.
      eapply sc_frame. 2: { symmetry; eassumption. }
      eassumption.

      symmetry in Heqtres. eapply IHk with (lS' := []) in Heqtres.
      destruct Heqtres. subst st; eassumption.
      econstructor. inversion H4; eassumption.
      inversion H2. inversion H9. eassumption.
      simpl. econstructor. eassumption.
      econstructor. inversion H2; eassumption.
      eapply sc_frame. 2: { symmetry; eassumption. }
      eassumption.

    * clear Hmt. change (S (length s1)) with (length ((v :: vabs_stack h s0 Second t c1 :: l0, n) :: s1)) in H.
      remember (teval_stack k
      (length ((v :: vabs_stack h s0 Second t c1 :: l0, n) :: s1))
      ((v :: vabs_stack h s0 Second t c1 :: l0, n) :: s1) h t c1) as tres.
      destruct tres.
      destruct o.
      2: { destruct c1; destruct c; tryfalse_invert. }
      destruct o.
      2: { destruct c1; destruct c; tryfalse_invert. }

      destruct c1; destruct c; inversion H; try (split; eauto); subst v0.

      eapply IHk with (lS' := []). simpl app.
      symmetry; eassumption.
      inversion H2. inversion H9; eassumption.
      simpl. econstructor. eassumption.
      econstructor. inversion H4; eassumption.
      econstructor. inversion H2; eassumption.
      eapply sc_frame. 2: { symmetry; eassumption. }
      eassumption.

      eapply subcl_wf; eauto.
      eapply IHk with (lS' := []). simpl app.
      symmetry; eassumption.
      inversion H2. inversion H9; eassumption.
      simpl. econstructor. eassumption.
      econstructor. inversion H4; eassumption.
      econstructor. inversion H2; eassumption.
      eapply sc_frame. 2: { symmetry; eassumption. }
      eassumption.
      
      eapply IHk with (lS' := []). simpl app.
      symmetry; eassumption.
      inversion H2. inversion H9; eassumption.
      simpl. econstructor. eassumption.
      econstructor. inversion H4; eassumption.
      econstructor. inversion H2; eassumption.
      eapply sc_frame. 2: { symmetry; eassumption. }
      eassumption.

      symmetry in Heqtres. eapply IHk with (lS' := []) in Heqtres.
      destruct Heqtres. subst st. eassumption.
      inversion H2. inversion H9; eassumption.
      simpl. econstructor. eassumption.
      econstructor. inversion H4; eassumption.
      econstructor. inversion H2; eassumption.
      eapply sc_frame. 2: { symmetry; eassumption. }
      eassumption.
  - destruct c; destruct fr; inversion H; split; eauto; constructor; constructor; eauto.
Qed.
