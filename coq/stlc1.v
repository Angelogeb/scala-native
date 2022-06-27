(* ############################################################ *)
(*                                                              *)
(*               Language definition for STLC  λ½q↩             *)
(*                                                              *)
(* ############################################################ *)

(* Starting point: https://github.com/TiarkRompf/scala-escape/blob/master/coq/stlc1.v *)

Require Export Arith.EqNat.
Require Export Arith.
Require Export List.
Require Export Lia.

Export ListNotations.

(* ############################################################ *)
(* Definitions                                                  *)
(* ############################################################ *)

(* ### Syntax ### *)

Definition id := nat.

Inductive class : Type :=
  | First  : class
  | Second : class
.

(* <: *)
Definition subcl (n m : class) :=
  match n, m with
  | First, Second => true
  | Second, First => false
  | _, _ => true
  end.

(* types *)
Inductive ty : Type :=
  | TBool  : ty
  | TFun   : ty -> class -> ty -> class -> ty
.

(* variables: 1st or 2nd class, using DeBrujin levels *)
Inductive var : Type :=
  | V : class -> id -> var
.

(* terms *)
Inductive tm : Type :=
  | ttrue  : tm
  | tfalse : tm
  | tvar   : var -> tm
  | tapp   : tm -> tm -> tm     (* f(x) *)
  | tabs   : class -> tm -> class -> tm  (* \f x.y *)
.

(* environments, split according to 1st/2nd class *)
Inductive env {X: Type} :=
  | Def (fc : list X) (sc : list X) (sc_min : nat).

(* values *)
Inductive vl : Type :=
  | vbool : bool -> vl
  | vabs  : @env vl -> class -> tm -> class -> vl
.

Definition venv := @env vl.  (* value environments *)
Definition tenv := @env ty.  (* type environments  *)

Global Hint Unfold venv : core.
Global Hint Unfold tenv : core.

(* environment lookup *)
Fixpoint index {X : Type} (n : id) (l : list X) : option X :=
  match l with
    | [] => None
    | a :: l'  => if beq_nat n (length l') then Some a else index n l'
  end.

Example indexEx1 : index 4 [1; 2; 3; 4; 5; 6] = Some 2.
Proof. reflexivity. Qed.

Definition lookup {X : Type} (n : var) (l : @env X) : option X :=
  match l with
    | Def l1 l2 m =>
         match n with
           | V First idx  => index idx l1
           | V Second idx => if m <=? idx then index idx l2 else None
         end
   end
.

Section env_tests.
  Let t1_1 := TBool.
  Let t1_0 := TFun TBool First TBool First.
  Let t2_0 := TBool.
  Let t2_1 := TFun TBool First TBool Second.
  Let t2_2 := TBool.
  Let t2_3 := TFun TBool Second TBool Second.

  Let sc_min := 1.

  Let example_env := Def [t1_1; t1_0] [t2_3; t2_2; t2_1; t2_0] sc_min.

  Example lookupEx1 :
    (lookup (V First 1) example_env) = Some t1_1 /\
    (lookup (V Second 2) example_env) = Some t2_2 /\
    (lookup (V Second 1) example_env = Some t2_1) /\
    (lookup (V Second 0) example_env = None (* Since 0 < sc_min *)).
  Proof.
    split; [ | split; [ | split]]; reflexivity.
  Qed.
End env_tests.

(* restrict visible bindings in environment *)
Definition sanitize_any {X : Type} (l : @env X) (n:nat): @env X :=
  match l with
    | Def l1 l2 _ => Def l1 l2 n
  end.

Definition sanitize_env {X : Type} (c : class) (l : @env X) : @env X :=
  match c,l  with
    | First, Def _ l2 _ => sanitize_any l (length l2)
    | Second, _ => l
  end.

(* add new binding to environment *)
Definition expand_env {X : Type} (l : @env X) (x : X) (c : class) : (@env X) :=
match l with
| Def l1 l2 m =>
   match c with
   | First => @Def X (x::l1) l2 m
   | Second => @Def X l1 (x::l2) m
   end
end
.


(* ### Type Assignment ### *)
(* Algorithmic version *)

Inductive has_type : tenv -> tm -> class -> ty -> Prop :=
| t_true: forall n env,
           has_type env ttrue n TBool
| t_false: forall n env,
           has_type env tfalse n TBool
| t_var: forall n x env T1,
           lookup x (sanitize_env n env) = Some T1 ->
           has_type env (tvar x) n T1
| t_app: forall m retcl q env f x T1 T2,
           has_type env f Second (TFun T1 m T2 retcl) ->
           has_type env x m T1 ->
           subcl retcl q = true ->
           has_type env (tapp f x) q T2
 | t_abs: forall m n retcl env y T1 T2,
           has_type (expand_env (expand_env (sanitize_env n env) (TFun T1 m T2 retcl) Second) T1 m) y retcl T2 ->
           has_type env (tabs m y retcl) n (TFun T1 m T2 retcl).

Definition get_inv_idx {X : Type} (env : @env X) :=
match env with
| Def l1 l2 idx => idx
end
.


Section has_type_tests.
  Let identity_ff := (tabs First (tvar (V First 0)) First).

  Example identity_type : forall q, has_type (Def [] [] 0) identity_ff q (TFun TBool First TBool First).
  Proof.
    intro q. destruct q.
    - apply t_abs. simpl. apply t_var. reflexivity.
    - apply t_abs. simpl. apply t_var. reflexivity.
  Qed.

  Let app_id_true := (tapp identity_ff ttrue).
  Example app_type : has_type (Def [] [] 0) app_id_true First TBool.
  Proof.
    apply t_app with (m := First) (T1 := TBool) (retcl := First).
    - apply identity_type.
    - apply t_true.
    - reflexivity.
  Qed.

  (* Infinite loop *)
  Example omega : exists T,
    has_type (Def [] [] 0)
      (tabs Second
        (tapp (tvar (V Second 0)) (tvar (V Second 1)))
        Second)
    First T.
  Proof.
    exists (TFun TBool Second TBool Second).
    apply t_abs. simpl. apply t_app with (m := Second) (T1 := TBool) (retcl := Second).
    - apply t_var. simpl. reflexivity.
    - apply t_var. simpl. reflexivity.
    - reflexivity.
  Qed.


  Lemma akin_to_weakening : forall n1 n2 t cl T fc sc,
    n2 <= n1 ->
    has_type (Def fc sc n1) t cl T ->
    has_type (Def fc sc n2) t cl T.
  Proof.
    intros. generalize dependent cl. generalize dependent T.
    generalize dependent fc. generalize dependent sc.
    induction t; intros; inversion H0; subst.
    + constructor.
    + constructor.
    + destruct cl; destruct v; destruct c; constructor; simpl in *; eauto.
      - case_eq (n1 <=? i); intro; rewrite H1 in H3.
        ++ assert (n2 <=? i = true). apply Nat.leb_le. apply Nat.leb_le in H1. lia. rewrite H2. assumption.
        ++ inversion H3.
    + econstructor. eapply IHt1. eassumption. eapply IHt2. eassumption. eassumption.
    + constructor. simpl in *. destruct cl; destruct c; simpl in *; eauto.
  Qed.

  Lemma has_type_c_any : forall fc sc sc_min t T, sc_min <= length sc -> has_type (Def fc sc sc_min) t First T -> has_type (Def fc sc sc_min) t Second T.
  Proof.
    intros fc sc sc_min t T Hlen HFirst.
    destruct t; inversion HFirst; subst; try constructor.
    - destruct v; destruct c; simpl in *; eauto.
      + case_eq (length sc <=? i); intro; rewrite H in H1; try inversion H1.
        ++ assert (sc_min <=? i = true). apply Nat.leb_le. apply Nat.leb_le in H. lia. rewrite H0. reflexivity.
    - econstructor; eauto. destruct retcl. reflexivity. reflexivity.
    - simpl in *. destruct c.
      all: apply akin_to_weakening with (n1 := length sc); eauto.
  Qed.
End has_type_tests.

(* ### Operational Semantics ### *)

(*
None             means timeout
Some None        means stuck
Some (Some v))   means result v
*)

(* eval^q *)
Fixpoint teval(k: nat)(env: venv)(t: tm)(n: class){struct k}: option (option vl) :=
  match k with
    | 0 => None
    | S k' =>
      match t with
      | ttrue      => Some (Some (vbool true))
      | tfalse     => Some (Some (vbool false))
      | tvar x     => Some (lookup x (sanitize_env n env))
      | tabs m y retcl => Some (Some (vabs (sanitize_env n env) m y retcl))
      | tapp ef ex   =>
         match teval k' env ef Second, n with
           | None, _ => None
           | Some None, _ => Some None
           | Some (Some (vbool _)), _ => Some None
           | Some (Some (vabs env2 m ey Second)), First => Some None
           | Some (Some (vabs env2 m ey retcl)), _ =>
              match teval k' env ex m with
                | None => None
                | Some None => Some None
                | Some (Some vx) =>
                teval k' (expand_env (expand_env env2 (vabs env2 m ey retcl) Second) vx m) ey retcl
              end
          end
      end
  end.



  Section teval_tests.

  (*
    NOTE

    1. λf^2(x^1).x^1 -> λ. 0^1
    2. λf^2(x^1).f^2 -> λ. 0^2  (* Although this term is ill-typed *)
    3. λf^2(x^2).x^2 -> λ. 1^2

    4. λf^2(x^2).λg^2(y^1).x^2 -> λ. 1^2
    5. λf^2(x^2).λg^2(y^1).y^1 -> λ. 0^1
    6. λf^2(x^2).λg^2(y^2).y^2 -> λ. 3^2
  *)

  Let mt : @env vl := (Def [] [] 0).

  Let c1 := (tapp (tabs First (tvar (V First 0)) First) ttrue).
  Let c3 := (tapp (tabs Second (tvar (V Second 1)) Second) ttrue).

  Let c4 :=
    (tapp
      (tapp
        (tabs Second (tabs First (tvar (V Second 1)) Second) Second)
        ttrue)
      tfalse).

  Let c5 :=
    (tapp
      (tapp
        (tabs Second (tabs First (tvar (V First 0)) Second) Second)
        ttrue)
      tfalse).

  Let c6 :=
    (tapp
      (tapp
        (tabs Second (tabs Second (tvar (V Second 3)) Second) Second)
        ttrue)
      tfalse).

  Example teval_test :
    teval 10 mt c1 First = Some (Some (vbool true)) /\
    teval 10 mt c3 Second = Some (Some (vbool true)) /\
    teval 10 mt c4 Second = Some (Some (vbool true)) /\
    teval 10 mt c5 Second = Some (Some (vbool false)) /\
    teval 10 mt c6 Second = Some (Some (vbool false)).
  Proof.
    split; [ | split; [ | split; [ | split ] ]]; simpl; reflexivity.
  Qed.
End teval_tests.


(* ############################################################ *)
(* Proofs                                                       *)
(* ############################################################ *)

(* ### Some helper lemmas ### *)

Global Hint Constructors ty : core.
Global Hint Constructors tm : core.
Global Hint Constructors vl : core.


Global Hint Constructors has_type : core.

Global Hint Constructors option : core.
Global Hint Constructors list : core.
Global Hint Constructors env : core.

Global Hint Unfold index : core.
Global Hint Unfold length : core.
Global Hint Unfold expand_env : core.
Global Hint Unfold lookup : core.
Global Hint Unfold index : core.
Global Hint Unfold sanitize_env : core.
Global Hint Unfold sanitize_any : core.

Global Hint Resolve ex_intro : core.

Definition length_env {X : Type} (c : class) (env : @env X): nat :=
match env, c with
| Def l1 l2 n, First => length l1
| Def l1 l2 n, Second => length l2
end
.

Definition get_class (x : var): class :=
match x with
| V c _ => c
end
.

Definition get_idx (x : var): nat :=
match x with
| V _ n => n
end
.

Lemma index_max : forall X vs n (T: X),
                       index n vs = Some T ->
                       n < length vs.
Proof.
  intros X vs n T HSome.
  induction vs; inversion HSome.
  - (* Cons *) case_eq (n =? length vs); intro n_eqs_len.
    + (* is head *) apply beq_nat_true in n_eqs_len. subst. constructor.
    + (* is in rest *)
      rewrite n_eqs_len in H0. apply IHvs in H0. simpl. lia.
Qed.

Lemma lookup_max : forall X vs x (T: X),
                       lookup x vs = Some T ->
                       get_idx x < length_env (get_class x) vs.
Proof.
  intros X vs x T HSome.
  destruct vs as [fc sc sc_min]. destruct x as [cl id].
  destruct cl; simpl; simpl in HSome.
  - (* cl = First *) eapply index_max. eassumption.
  - (* cl = Second *) destruct (sc_min <=? id).
    + (* Same as cl = First*) eapply index_max. eassumption.
    + (* lookup returns None, impossible *) discriminate HSome.
Qed.
