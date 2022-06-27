Require Export LibTactics.
Require Export Arith.EqNat.
Require Export Arith.Le.
Require Export Arith.Lt.
Require Export Arith.Compare_dec.
Require Import Coq.Program.Equality.
Require Export List.
Require Export Lia.

Export ListNotations.

(* ### Syntax ### *)

Definition id := nat.

Inductive class : Type :=
  | First : class
  | Second : class
.

Inductive subcl : class -> class -> Prop :=
| subcl_refl : forall c, subcl c c
| subcl_top  : forall c, subcl c Second.

Definition subcl_trans : forall c1 c2 c3, subcl c1 c2 -> subcl c2 c3 -> subcl c1 c3.
Proof. intros. destruct c1; destruct c2; destruct c3; eauto; econstructor. Qed.

(* term variables occurring in types *)
Inductive var : Type :=
| varF : id -> var (* free, in concrete environment *)
| varH : id -> var (* free, in abstract environment  *)
| varB : id -> var (* locally-bound variable *)
.

Inductive ty : Type :=
| TTop : ty
| TBot : ty
(* (z: T) -> T^z *)
| TAll : ty -> class -> ty -> class -> ty
(* x.Type *)
| TSel : var -> ty
(* { Type: S..U } *)
| TMem : ty(*S*) -> ty(*U*) -> ty
.

Inductive tm : Type :=
(* x -- free variable, matching concrete environment *)
| tvar : id -> tm
(* { Type = T } *)
| ttyp : ty -> tm
(* lambda x:T.t *)
| tabs : ty -> class -> tm -> class -> tm
(* t t *)
| tapp : tm -> tm -> tm
.


(* ### Environments ### *)

(* An environment is a list of bindings, where each
   binding has a boolean flag "is-available", and
   a 1st/2nd class identifier. *)

Definition env X := list  (bool * class * X).

Inductive vl : Type :=
(* a closure for a lambda abstraction *)
| vabs : env vl (*H*) -> ty -> class -> tm -> class -> vl
(* a closure for a first-class type *)
| vty : env vl (*H*) -> ty -> vl
.

Definition tenv := env ty. (* Gamma environment: static *)
Definition venv := env vl. (* H environment: run-time *)
Definition aenv := env (venv*ty). (* J environment: abstract at run-time *)

(* ### Representation of Bindings ### *)

Fixpoint indexr {X : Type} (n : id) (l : list X) : option X :=
  match l with
    | [] => None
    | a :: l' =>
      if (beq_nat n (length l')) then Some a else indexr n l'
  end.

Inductive closed: nat(*B*) -> nat(*H*) -> nat(*F*) -> ty -> Prop :=
| cl_top: forall i j k,
    closed i j k TTop
| cl_bot: forall i j k,
    closed i j k TBot
| cl_all: forall i j k T1 T2 c1 c2,
    closed i j k T1 ->
    closed (S i) j k T2 ->
    closed i j k (TAll T1 c1 T2 c2)
| cl_sel: forall i j k x,
    k > x ->
    closed i j k (TSel (varF x))
| cl_selh: forall i j k x,
    j > x ->
    closed i j k (TSel (varH x))
| cl_selb: forall i j k x,
    i > x ->
    closed i j k (TSel (varB x))
| cl_mem: forall i j k T1 T2,
    closed i j k T1 ->
    closed i j k T2 ->
    closed i j k (TMem T1 T2)
.

(* open define a locally-nameless encoding wrt to TVarB type variables. *)
(* substitute var u for all occurrences of (varB k) *)
Fixpoint open_rec (k: nat) (u: var) (T: ty) { struct T }: ty :=
  match T with
    | TTop            => TTop
    | TBot            => TBot
    | TAll T1 c1 T2 c2 => TAll (open_rec k u T1) c1 (open_rec (S k) u T2) c2
    | TSel (varF x) => TSel (varF x)
    | TSel (varH i) => TSel (varH i)
    | TSel (varB i) => if beq_nat k i then TSel u else TSel (varB i)
    | TMem T1 T2      => TMem (open_rec k u T1) (open_rec k u T2)
  end.

Definition open u T := open_rec 0 u T.

(* Locally-nameless encoding with respect to varH variables. *)
Fixpoint subst (U : var) (T : ty) {struct T} : ty :=
  match T with
    | TTop            => TTop
    | TBot            => TBot
    | TAll T1 c1 T2 c2    => TAll (subst U T1) c1 (subst U T2) c2
    | TSel (varB i) => TSel (varB i)
    | TSel (varF i) => TSel (varF i)
    | TSel (varH i) => if beq_nat i 0 then TSel U else TSel (varH (i-1))
    | TMem T1 T2      => TMem (subst U T1) (subst U T2)
  end.

Fixpoint nosubst (T : ty) {struct T} : Prop :=
  match T with
    | TTop            => True
    | TBot            => True
    | TAll T1 c1 T2 c2 => nosubst T1 /\ nosubst T2
    | TSel (varB i) => True
    | TSel (varF i) => True
    | TSel (varH i) => i <> 0
    | TMem T1 T2    => nosubst T1 /\ nosubst T2
  end.


Definition sanitize_env {X} (c : class) (l: env X)  := 
  match c with
    | First =>
      map (fun p =>
             match p with
               | (true, First, x) => (true, First, x)
               | (true, Second, x) => (false, Second, x)
               | (false, c, x) => (false, c, x)
             end) l
    | Second => l
  end.


(* ### Static Subtyping ### *)
(*
The first env is for looking up varF variables.
The first env matches the concrete runtime environment, and is
extended during type assignment.

The second env is for looking up varH variables.
The second env matches the abstract runtime environment, and is
extended during subtyping.
*)
Inductive stp: tenv -> tenv -> ty -> ty -> Prop :=
| stp_top: forall G1 GH T1,
    closed 0 (length GH) (length G1) T1 ->
    stp G1 GH T1 TTop
| stp_bot: forall G1 GH T2,
    closed 0 (length GH) (length G1) T2 ->
    stp G1 GH TBot T2
| stp_mem: forall G1 GH S1 U1 S2 U2,
    stp G1 GH U1 U2 ->
    stp G1 GH S2 S1 ->
    stp G1 GH (TMem S1 U1) (TMem S2 U2)
| stp_sel1: forall G1 GH TX T2 x a c,
    indexr x G1 = Some (a,c,TX) ->
    closed 0 0 (length G1) TX ->
    stp G1 GH TX (TMem TBot T2) ->
    stp G1 GH (TSel (varF x)) T2
| stp_sel2: forall G1 GH TX T1 x a c,
    indexr x G1 = Some (a, c, TX) ->
    closed 0 0 (length G1) TX ->
    stp G1 GH TX (TMem T1 TTop) ->
    stp G1 GH T1 (TSel (varF x))
| stp_selx: forall G1 GH v x a c,
    (* This is a bit looser than just being able to select on TMem vars. *)
    indexr x G1 = Some (a,c,v) ->
    stp G1 GH (TSel (varF x)) (TSel (varF x))
| stp_sela1: forall G1 GH TX T2 x a c,
    indexr x GH = Some (a,c,TX) ->
    closed 0 x (length G1) TX ->
    stp G1 GH TX (TMem TBot T2) ->
    stp G1 GH (TSel (varH x)) T2
| stp_sela2: forall G1 GH TX T1 x a c,
    indexr x GH = Some (a,c,TX) ->
    closed 0 x (length G1) TX ->
    stp G1 GH TX (TMem T1 TTop) ->
    stp G1 GH T1 (TSel (varH x))
| stp_selax: forall G1 GH v x a c,
    (* This is a bit looser than just being able to select on TMem vars. *)
    indexr x GH = Some (a,c,v)  ->
    stp G1 GH (TSel (varH x)) (TSel (varH x))
| stp_all: forall G1 GH T1 T2 T3 T4 x c c2 c4,
    subcl c2 c4 ->
    stp G1 GH T3 T1 ->
    x = length GH ->
    closed 1 (length GH) (length G1) T2 ->
    closed 1 (length GH) (length G1) T4 ->
    stp G1 ((true,c,T3)::GH) (open (varH x) T2) (open (varH x) T4) ->
    stp G1 GH (TAll T1 c T2 c2) (TAll T3 c T4 c4)
.

(* ### Type Assignment ### *)
Inductive has_type : tenv -> tm -> class -> ty -> Prop :=
| t_var: forall x env T1 c c1,
           indexr x (sanitize_env c env) = Some (true,c1,T1) ->
           stp env [] T1 T1 ->
           has_type env (tvar x) c T1
| t_typ: forall env T1 c,
           closed 0 0 (length env) T1 ->
           has_type env (ttyp T1) c (TMem T1 T1)
| t_app: forall env f x T1 T2 c1 c2,
           has_type env f Second (TAll T1 c1 T2 c2) ->
           has_type env x c1 T1 ->
           closed 0 0 (length env) T2 ->
           has_type env (tapp f x) c2 T2
| t_dapp:forall env f x T1 T2 T cf cr,
           has_type env f Second (TAll T1 cf T2 cr) ->
           has_type env (tvar x) cf T1 ->
           T = open (varF x) T2 ->
           closed 0 0 (length env) T ->
           has_type env (tapp f (tvar x)) cr T
| t_abs: forall env y T1 T2 c cf cr,
           has_type ((true,cf,T1)::(sanitize_env c env)) y cr (open (varF (length env)) T2) ->
           closed 0 0 (length env) (TAll T1 cf T2 cr) ->
           has_type env (tabs T1 cf y cr) c (TAll T1 cf T2 cr)
| t_sub: forall env e T1 T2 c,
           has_type env e c T1 ->
           stp env [] T1 T2 ->
           has_type env e c T2
.

Definition base (v:vl): venv :=
  match v with
    | vty GX _ => GX
    | vabs GX _ _ _ _ => GX
  end.

(* ### Runtime Subtyping ### *)
(* H1 T1 <: H2 T2 -| J *)
Inductive stp2: bool (* whether selections are precise *) ->
                bool (* whether the last rule may not be transitivity *) ->
                venv -> ty -> venv -> ty -> aenv  ->
                nat (* derivation size *) ->
                Prop :=
| stp2_top: forall G1 G2 GH T s n,
    closed 0 (length GH) (length G1) T ->
    stp2 s true G1 T G2 TTop GH (S n)
| stp2_bot: forall G1 G2 GH T s n,
    closed 0 (length GH) (length G2) T ->
    stp2 s true G1 TBot G2 T GH (S n)
| stp2_mem: forall G1 G2 S1 U1 S2 U2 GH s n1 n2,
    stp2 s s G1 U1 G2 U2 GH n1 ->
    stp2 s false G2 S2 G1 S1 GH n2 ->
    stp2 s true G1 (TMem S1 U1) G2 (TMem S2 U2) GH (S (n1+n2))

(* concrete type variables *)
(* precise/invertible bounds *)
(* vty already marks binding as type binding, so no need for additional TMem marker *)
| stp2_strong_sel1: forall G1 G2 GX TX x T2 GH n1 a c,
    indexr x G1 = Some (a, c, vty GX TX) ->
    val_type GX (vty GX TX) (TMem TX TX) -> (* for downgrade *)
    closed 0 0 (length GX) TX ->
    stp2 true true GX TX G2 T2 GH n1 ->
    stp2 true true G1 (TSel (varF x)) G2 T2 GH (S n1)
| stp2_strong_sel2: forall G1 G2 GX TX x T1 GH n1 a c,
    indexr x G2 = Some (a, c, vty GX TX) ->
    val_type GX (vty GX TX) (TMem TX TX) -> (* for downgrade *)
    closed 0 0 (length GX) TX ->
    stp2 true false G1 T1 GX TX GH n1 ->
    stp2 true true G1 T1 G2 (TSel (varF x)) GH (S n1)
(* imprecise type *)
| stp2_sel1: forall G1 G2 v TX x T2 GH n1 a c,
    indexr x G1 = Some (a, c,v) ->
    val_type (base v) v TX ->
    closed 0 0 (length (base v)) TX ->
    stp2 false false (base v) TX G2 (TMem TBot T2) GH n1 ->
    stp2 false true G1 (TSel (varF x)) G2 T2 GH (S n1)
| stp2_sel2: forall G1 G2 v TX x T1 GH n1 a c,
    indexr x G2 = Some (a,c,v) ->
    val_type (base v) v TX ->
    closed 0 0 (length (base v)) TX ->
    stp2 false false (base v) TX G1 (TMem T1 TTop) GH n1 ->
    stp2 false true G1 T1 G2 (TSel (varF x)) GH (S n1)
| stp2_selx: forall G1 G2 v x1 x2 GH s n a1 c1 a2 c2,
    indexr x1 G1 = Some (a1,c1,v) ->
    indexr x2 G2 = Some (a2,c2,v) ->
    stp2 s true G1 (TSel (varF x1)) G2 (TSel (varF x2)) GH (S n)

(* abstract type variables *)
| stp2_sela1: forall G1 G2 GX TX x T2 GH n1 a c,
    indexr x GH = Some (a, c, (GX, TX)) ->
    closed 0 x (length GX) TX ->
    stp2 false false GX TX G2 (TMem TBot T2) GH n1 ->
    stp2 false true G1 (TSel (varH x)) G2 T2 GH (S n1)
| stp2_sela2: forall G1 G2 GX T1 TX x GH n1 a c,
    indexr x GH = Some (a, c, (GX, TX)) ->
    closed 0 x (length GX) TX ->
    stp2 false false GX TX G1 (TMem T1 TTop) GH n1 ->
    stp2 false true G1 T1 G2 (TSel (varH x)) GH (S n1)
| stp2_selax: forall G1 G2 v x GH s n,
    indexr x GH = Some v ->
    stp2 s true G1 (TSel (varH x)) G2 (TSel (varH x)) GH (S n)

| stp2_all: forall G1 G2 T1 T2 T3 T4 x GH s n1 n2 c c2 c4,
    subcl c2 c4 ->
    stp2 false false G2 T3 G1 T1 GH n1 ->
    x = length GH ->
    closed 1 (length GH) (length G1) T2 ->
    closed 1 (length GH) (length G2) T4 ->
    stp2 false false G1 (open (varH x) T2) G2 (open (varH x) T4) ((true, c, (G2, T3))::GH) n2 ->
    stp2 s true G1 (TAll T1 c T2 c2) G2 (TAll T3 c T4 c4) GH (S (n1 + n2))

| stp2_wrapf: forall G1 G2 T1 T2 GH s n1,
    stp2 s true G1 T1 G2 T2 GH n1 ->
    stp2 s false G1 T1 G2 T2 GH (S n1)

| stp2_transf: forall G1 G2 G3 T1 T2 T3 GH s n1 n2,
    stp2 s true G1 T1 G2 T2 GH n1 ->
    stp2 s false G2 T2 G3 T3 GH n2 ->
    stp2 s false G1 T1 G3 T3 GH (S (n1+n2))

(* consistent environment *)
with wf_env : venv -> tenv -> Prop :=
| wfe_nil : wf_env nil nil
| wfe_cons : forall v t vs ts a c,
    val_type ((a,c,v)::vs) v t ->
    wf_env vs ts ->
    wf_env (cons (a,c,v) vs) (cons (a,c,t) ts)

(* value type assignment *)
with val_type : venv -> vl -> ty -> Prop :=
| v_ty: forall env venv tenv T1 TE,
    wf_env venv tenv ->
    (exists n, stp2 true true venv (TMem T1 T1) env TE [] n) ->
    val_type env (vty venv T1) TE
| v_abs: forall env venv tenv x y T1 T2 TE c1 c2,
    wf_env venv tenv ->
    has_type ((true,c1,T1)::tenv) y c2 (open (varF x) T2) ->
    length venv = x ->
    (exists n, stp2 true true venv (TAll T1 c1 T2 c2) env TE [] n) ->
    val_type env (vabs venv T1 c1 y c2) TE
(* | v_abs_2 :
    val_type env (vabs venv ....) TE ->
    (indexr venv -> venv') ->
    val_type evn (vabs venv' ....) TE *)
.

Inductive wf_envh : venv -> aenv -> tenv -> Prop :=
| wfeh_nil : forall vvs, wf_envh vvs nil nil
| wfeh_cons : forall t vs vvs ts a c,
    wf_envh vvs vs ts ->
    wf_envh vvs (cons (a,c,(vvs,t)) vs) (cons (a,c,t) ts)
.

Inductive valh_type : venv -> aenv -> (venv*ty) -> ty -> Prop :=
| v_tya: forall aenv venv T1,
    valh_type venv aenv (venv, T1) T1
.

(* ### Evaluation (Big-Step Semantics) ### *)

(*
None             means timeout
Some None        means stuck
Some (Some v))   means result v

Could use do-notation to clean up syntax.
*)

Fixpoint teval(n: nat)(env: venv)(t: tm)(ct: class){struct n}: option (option vl) :=
  match n with
    | 0 => None
    | S n =>
      match t with
        | tvar x       => Some (match indexr x (sanitize_env ct env) with
                                  | Some (true,_,x) => Some x
                                  | _ => None
                                end)
        | ttyp T       => Some (Some (vty env T))
        | tabs T c1 y c2  => Some (Some (vabs (sanitize_env ct env) T c1 y c2))
        | tapp ef ex   =>
          match teval n env ef Second with
            | None => None
            | Some None => Some None
            | Some (Some (vty _ _)) => Some None
            | Some (Some (vabs env2 _ c1 ey c2)) =>
              match teval n env ex c1 with
                | None => None
                | Some None => Some None
                | Some (Some vx) =>
                  teval n ((true,c1,vx)::env2) ey c2
              end
          end
      end
  end.

(* automation *)
Global Hint Unfold venv : core.
Global Hint Unfold tenv : core.

Global Hint Unfold open : core.
Global Hint Unfold indexr : core.
Global Hint Unfold length : core.

Global Hint Constructors subcl : core.
Global Hint Constructors ty : core.
Global Hint Constructors tm : core.
Global Hint Constructors vl : core.

Global Hint Constructors closed : core.
Global Hint Constructors has_type : core.
Global Hint Constructors val_type : core.
Global Hint Constructors wf_env : core.
Global Hint Constructors wf_envh : core.
Global Hint Constructors stp : core.
Global Hint Constructors stp2 : core.

Global Hint Constructors option : core.
Global Hint Constructors list : core.

Global Hint Resolve ex_intro : core.

Global Hint Unfold env : core.

(* ############################################################ *)
(* Proofs *)
(* ############################################################ *)

Fixpoint tsize(T: ty) :=
  match T with
    | TTop => 1
    | TBot => 1
    | TAll T1 c1 T2 c2 => S (tsize T1 + tsize T2)
    | TSel _ => 1
    | TMem T1 T2 => S (tsize T1 + tsize T2)
  end.

Lemma open_preserves_size: forall T x j,
  tsize T = tsize (open_rec j (varH x) T).
Proof.
  intros T. induction T; intros; simpl; eauto.
  - destruct v; simpl; destruct (beq_nat j i); eauto.
Qed.

(* ## Extension, Regularity ## *)

Lemma wf_length : forall vs ts,
                    wf_env vs ts ->
                    (length vs = length ts).
Proof.
  intros. induction H. auto.
  compute. eauto. 
Qed.

Global Hint Immediate wf_length : core.

Lemma wfh_length : forall vvs vs ts,
                    wf_envh vvs vs ts ->
                    (length vs = length ts).
Proof.
  intros. induction H. auto.
  compute. eauto. 
Qed.

Global Hint Immediate wfh_length : core.

Lemma indexr_max : forall X vs n (T: X),
                       indexr n vs = Some T ->
                       n < length vs.
Proof.
  intros X vs. induction vs.
  - (* "nil" *) intros. inversion H.
  - (* "cons" *)
    intros. inversion H.
    case_eq (beq_nat n (length vs)); intros E2.
    + (* "hit" *)
      eapply beq_nat_true in E2. subst n. compute. eauto.
    + (* "miss" *)
      rewrite E2 in H1.
      assert (n < length vs). eapply IHvs. apply H1.
      compute. eauto.
Qed.

Lemma le_xx : forall a b,
                       a <= b ->
                       exists E, le_lt_dec a b = left E.
Proof. intros.
  case_eq (le_lt_dec a b). intros. eauto.
  intros. lia.
Qed.
Lemma le_yy : forall a b,
                       a > b ->
                       exists E, le_lt_dec a b = right E.
Proof. intros.
  case_eq (le_lt_dec a b). intros. lia.
  intros. eauto.
Qed.

Lemma indexr_extend : forall X vs n x (T: X),
                       indexr n vs = Some T ->
                       indexr n (x::vs) = Some T.

Proof.
  intros.
  assert (n < length vs). eapply indexr_max. eauto.
  assert (beq_nat n (length vs) = false) as E. eapply beq_nat_false_iff. lia.
  unfold indexr. unfold indexr in H. rewrite H. rewrite E. reflexivity.
Qed.

(* splicing -- for stp_extend. *)

Fixpoint splice n (T : ty) {struct T} : ty :=
  match T with
    | TTop         => TTop
    | TBot         => TBot
    | TAll T1 c1 T2 c2   => TAll (splice n T1) c1 (splice n T2) c2
    | TSel (varF i) => TSel (varF i)
    | TSel (varB i) => TSel (varB i)
    | TSel (varH i) => if le_lt_dec n i then TSel (varH (i+1)) else TSel (varH i)
    | TMem T1 T2      => TMem (splice n T1) (splice n T2)
  end.

Definition spliceat n (V: (bool*class*(venv*ty))) :=
  match V with
    | (a,c,(G,T)) => (a,c,(G,splice n T))
  end.

Definition spliceb n (V: (bool*class*ty)) :=
  match V with
    | (a,c,T) => (a,c,splice n T)
  end.


Lemma splice_open_permute: forall {X} (G0:list X) T2 n j,
(open_rec j (varH (n + S (length G0))) (splice (length G0) T2)) =
(splice (length G0) (open_rec j (varH (n + length G0)) T2)).
Proof.
  intros X G T. induction T; intros; simpl; eauto;
  try rewrite IHT1; try rewrite IHT2; try rewrite IHT; eauto;
  destruct v; eauto.

  case_eq (le_lt_dec (length G) i); intros E LE; simpl; eauto.
  rewrite LE. eauto.
  rewrite LE. eauto.
  case_eq (beq_nat j i); intros E; simpl; eauto.
  case_eq (le_lt_dec (length G) (n + length G)); intros EL LE.
  rewrite E.
  assert (n + S (length G) = n + length G + 1). lia.
  rewrite H. eauto.
  lia.
  rewrite E. eauto.
Qed.

Lemma indexr_splice_hi: forall G0 G2 x0 v1 T,
    indexr x0 (G2 ++ G0) = Some T ->
    length G0 <= x0 ->
    indexr (x0 + 1) (map (splice (length G0)) G2 ++ v1 :: G0) = Some (splice (length G0) T).
Proof.
  intros G0 G2. induction G2; intros.
  - eapply indexr_max in H. simpl in H. lia.
  - simpl in H.
    case_eq (beq_nat x0 (length (G2 ++ G0))); intros E.
    + rewrite E in H. inversion H. subst. simpl.
      rewrite app_length in E.
      rewrite app_length. rewrite map_length. simpl.
      assert (beq_nat (x0 + 1) (length G2 + S (length G0)) = true). {
        eapply beq_nat_true_iff. eapply beq_nat_true_iff in E. lia.
      }
      rewrite H1. eauto.
    + rewrite E in H.  eapply IHG2 in H. eapply indexr_extend. eapply H. eauto.
Qed.

Lemma indexr_spliceat_hi: forall G0 G2 x0 v1 G T a c,
    indexr x0 (G2 ++ G0) = Some (a,c,(G, T)) ->
    length G0 <= x0 ->
    indexr (x0 + 1) (map (spliceat (length G0)) G2 ++ v1 :: G0) =
    Some (a,c,(G, splice (length G0) T)).
Proof.
  intros G0 G2. induction G2; intros.
  - eapply indexr_max in H. simpl in H. lia.
  - simpl in H. destruct a.
    case_eq (beq_nat x0 (length (G2 ++ G0))); intros E.
    + rewrite E in H. inversion H. subst. simpl.
      rewrite app_length in E.
      rewrite app_length. rewrite map_length. simpl.
      assert (beq_nat (x0 + 1) (length G2 + S (length G0)) = true). {
        eapply beq_nat_true_iff. eapply beq_nat_true_iff in E. lia.
      }
      rewrite H1. eauto.
    + rewrite E in H.  eapply IHG2 in H. eapply indexr_extend. eapply H. eauto.
Qed.

Lemma indexr_spliceb_hi: forall G0 G2 x0 v1 G T,
    indexr x0 (G2 ++ G0) = Some (G, T) ->
    length G0 <= x0 ->
    indexr (x0 + 1) (map (spliceb (length G0)) G2 ++ v1 :: G0) =
    Some (G, splice (length G0) T).
Proof.
  intros G0 G2. induction G2; intros.
  - eapply indexr_max in H. simpl in H. lia.
  - simpl in H. destruct a. destruct p.
    case_eq (beq_nat x0 (length (G2 ++ G0))); intros E.
    + rewrite E in H. inversion H. subst. simpl.
      rewrite app_length in E.
      rewrite app_length. rewrite map_length. simpl.
      assert (beq_nat (x0 + 1) (length G2 + S (length G0)) = true). {
        eapply beq_nat_true_iff. eapply beq_nat_true_iff in E. lia.
      }
      rewrite H1. eauto.
    + rewrite E in H.  eapply IHG2 in H. eapply indexr_extend. eapply H. eauto.
Qed.

Lemma plus_lt_contra: forall a b,
  a + b < b -> False.
Proof.
  intros a b H. induction a.
  - simpl in H. apply lt_irrefl in H. assumption.
  - simpl in H. apply IHa. lia.
Qed.

Lemma indexr_splice_lo0: forall {X} G0 G2 x0 (T:X),
    indexr x0 (G2 ++ G0) = Some T ->
    x0 < length G0 ->
    indexr x0 G0 = Some T.
Proof.
  intros X G0 G2. induction G2; intros.
  - simpl in H. apply H.
  - simpl in H.
    case_eq (beq_nat x0 (length (G2 ++ G0))); intros E.
    + eapply beq_nat_true_iff in E. subst.
      rewrite app_length in H0. apply plus_lt_contra in H0. inversion H0.
    + rewrite E in H. apply IHG2. apply H. apply H0.
Qed.

Lemma indexr_extend_mult: forall {X} G0 G2 x0 (T:X),
    indexr x0 G0 = Some T ->
    indexr x0 (G2++G0) = Some T.
Proof.
  intros X G0 G2. induction G2; intros.
  - simpl. assumption.
  - simpl.
    case_eq (beq_nat x0 (length (G2 ++ G0))); intros E.
    + eapply beq_nat_true_iff in E.
      apply indexr_max in H. subst.
      rewrite app_length in H. apply plus_lt_contra in H. inversion H.
    + apply IHG2. assumption.
Qed.

Lemma indexr_splice_lo: forall G0 G2 x0 v1 T f,
    indexr x0 (G2 ++ G0) = Some T ->
    x0 < length G0 ->
    indexr x0 (map (splice f) G2 ++ v1 :: G0) = Some T.
Proof.
  intros.
  assert (indexr x0 G0 = Some T). eapply indexr_splice_lo0; eauto.
  eapply indexr_extend_mult. eapply indexr_extend. eauto.
Qed.

Lemma indexr_spliceat_lo: forall G0 G2 x0 v1 G T f,
    indexr x0 (G2 ++ G0) = Some (G, T) ->
    x0 < length G0 ->
    indexr x0 (map (spliceat f) G2 ++ v1 :: G0) = Some (G, T).
Proof.
  intros.
  assert (indexr x0 G0 = Some (G, T)). eapply indexr_splice_lo0; eauto.
  eapply indexr_extend_mult. eapply indexr_extend. eauto.
Qed.
Lemma indexr_spliceb_lo: forall G0 G2 x0 v1 G T f,
    indexr x0 (G2 ++ G0) = Some (G, T) ->
    x0 < length G0 ->
    indexr x0 (map (spliceb f) G2 ++ v1 :: G0) = Some (G, T).
Proof.
  intros.
  assert (indexr x0 G0 = Some (G, T)). eapply indexr_splice_lo0; eauto.
  eapply indexr_extend_mult. eapply indexr_extend. eauto.
Qed.

Lemma closed_splice: forall i j k T n,
  closed i j k T ->
  closed i (S j) k (splice n T).
Proof.
  intros. induction H; simpl; eauto.
  case_eq (le_lt_dec n x); intros E LE.
  apply cl_selh. lia.
  apply cl_selh. lia.
Qed.

Lemma map_splice_length_inc: forall G0 G2 v1,
   (length (map (splice (length G0)) G2 ++ v1 :: G0)) = (S (length (G2 ++ G0))).
Proof.
  intros. rewrite app_length. rewrite map_length. induction G2.
  - simpl. reflexivity.
  - simpl. eauto.
Qed.

Lemma map_spliceat_length_inc: forall G0 G2 v1,
   (length (map (spliceat (length G0)) G2 ++ v1 :: G0)) = (S (length (G2 ++ G0))).
Proof.
  intros. rewrite app_length. rewrite map_length. induction G2.
  - simpl. reflexivity.
  - simpl. eauto.
Qed.

Lemma map_spliceb_length_inc: forall G0 G2 v1,
   (length (map (spliceb (length G0)) G2 ++ v1 :: G0)) = (S (length (G2 ++ G0))).
Proof.
  intros. rewrite app_length. rewrite map_length. induction G2.
  - simpl. reflexivity.
  - simpl. eauto.
Qed.

Lemma closed_inc_mult: forall i j k T,
  closed i j k T ->
  forall i' j' k',
  i' >= i -> j' >= j -> k' >= k ->
  closed i' j' k' T.
Proof.
  intros i j k T H. induction H; intros; eauto; try solve [constructor; lia].
  - apply cl_all. apply IHclosed1; lia. apply IHclosed2; lia.
Qed.

Lemma closed_inc: forall i j k T,
  closed i j k T ->
  closed i (S j) k T.
Proof.
  intros. apply (closed_inc_mult i j k T H i (S j) k); lia.
Qed.

Lemma closed_splice_idem: forall i j k T n,
                            closed i j k T ->
                            n >= j ->
                            splice n T = T.
Proof.
  intros. induction H; eauto.
  - (* TAll *) simpl.
    rewrite IHclosed1. rewrite IHclosed2.
    reflexivity.
    assumption. assumption.
  - (* TVarH *) simpl.
    case_eq (le_lt_dec n x); intros E LE. lia. reflexivity.
  - (* TMem *) simpl.
    rewrite IHclosed1. rewrite IHclosed2.
    reflexivity.
    assumption. assumption.
Qed.

Ltac ev := repeat match goal with
                    | H: exists _, _ |- _ => destruct H
                    | H: _ /\  _ |- _ => destruct H
           end.

Ltac inv_mem := match goal with
                  | H: closed 0 (length ?GH) (length ?G) (TMem ?T1 ?T2) |-
                    closed 0 (length ?GH) (length ?G) ?T2 => inversion H; subst; eauto
                  | H: closed 0 (length ?GH) (length ?G) (TMem ?T1 ?T2) |-
                    closed 0 (length ?GH) (length ?G) ?T1 => inversion H; subst; eauto
                end.

Lemma stp_closed : forall G GH T1 T2,
                     stp G GH T1 T2 ->
                     closed 0 (length GH) (length G) T1 /\ closed 0 (length GH) (length G) T2.
Proof.
  intros. induction H;
    try solve [repeat ev; split; try inv_mem; eauto using indexr_max].
Qed.

Lemma stp_closed2 : forall G1 GH T1 T2,
                       stp G1 GH T1 T2 ->
                       closed 0 (length GH) (length G1) T2.
Proof.
  intros. apply (proj2 (stp_closed G1 GH T1 T2 H)).
Qed.

Lemma stp_closed1 : forall G1 GH T1 T2,
                       stp G1 GH T1 T2 ->
                       closed 0 (length GH) (length G1) T1.
Proof.
  intros. apply (proj1 (stp_closed G1 GH T1 T2 H)).
Qed.

Lemma stp2_closed: forall G1 G2 T1 T2 GH s m n,
                     stp2 s m G1 T1 G2 T2 GH n ->
                     closed 0 (length GH) (length G1) T1 /\ closed 0 (length GH) (length G2) T2.
  intros. induction H;
    try solve [repeat ev; split; try inv_mem; eauto using indexr_max].
Qed.

Lemma stp2_closed2 : forall G1 G2 T1 T2 GH s m n,
                       stp2 s m G1 T1 G2 T2 GH n ->
                       closed 0 (length GH) (length G2) T2.
Proof.
  intros. apply (proj2 (stp2_closed G1 G2 T1 T2 GH s m n H)).
Qed.

Lemma stp2_closed1 : forall G1 G2 T1 T2 GH s m n,
                       stp2 s m G1 T1 G2 T2 GH n ->
                       closed 0 (length GH) (length G1) T1.
Proof.
  intros. apply (proj1 (stp2_closed G1 G2 T1 T2 GH s m n H)).
Qed.

Lemma closed_upgrade: forall i j k i' T,
 closed i j k T ->
 i' >= i ->
 closed i' j k T.
Proof.
 intros. apply (closed_inc_mult i j k T H i' j k); lia.
Qed.

Lemma closed_upgrade_free: forall i j k j' T,
 closed i j k T ->
 j' >= j ->
 closed i j' k T.
Proof.
 intros. apply (closed_inc_mult i j k T H i j' k); lia.
Qed.

Lemma closed_upgrade_freef: forall i j k k' T,
 closed i j k T ->
 k' >= k ->
 closed i j k' T.
Proof.
 intros. apply (closed_inc_mult i j k T H i j k'); lia.
Qed.

Lemma closed_open: forall i j k V T, closed (i+1) j k T -> closed i j k (TSel V) ->
  closed i j k (open_rec i V T).
Proof.
  intros. generalize dependent i.
  induction T; intros; inversion H;
  try econstructor;
  try eapply IHT1; eauto; try eapply IHT2; eauto; try eapply IHT; eauto.
  eapply closed_upgrade. eauto. eauto.
  - (* "TVarB" *) simpl.
    case_eq (beq_nat i x); intros E. eauto.
    econstructor. eapply beq_nat_false_iff in E. lia.
Qed.

Lemma indexr_has: forall X (G: list X) x,
  length G > x ->
  exists v, indexr x G = Some v.
Proof.
  intros. remember (length G) as n.
  generalize dependent x.
  generalize dependent G.
  induction n; intros; try lia.
  destruct G; simpl.
  - simpl in Heqn. inversion Heqn.
  - simpl in Heqn. inversion Heqn. subst.
    case_eq (beq_nat x (length G)); intros E.
    + eexists. reflexivity.
    + apply beq_nat_false in E. apply IHn; eauto.
      lia.
Qed.

Lemma stp_refl_aux: forall n T G GH,
  closed 0 (length GH) (length G) T ->
  tsize T < n ->
  stp G GH T T.
Proof.
  intros n. induction n; intros; try lia.
  inversion H; subst; eauto;
  try solve [lia];
  try solve [simpl in H0; constructor; apply IHn; eauto; try lia];
  try solve [apply indexr_has in H1; destruct H1; destruct x0; destruct p; eauto].
  - simpl in H0.
    eapply stp_all. eauto. eauto.
    eapply IHn; eauto; try lia.
    reflexivity.
    assumption.
    assumption.
    apply IHn; eauto.
    simpl. apply closed_open; auto using closed_inc.
    unfold open. rewrite <- open_preserves_size. lia.
Qed.

Lemma stp_refl: forall T G GH,
  closed 0 (length GH) (length G) T ->
  stp G GH T T.
Proof.
  intros. apply stp_refl_aux with (n:=S (tsize T)); eauto.
Qed.

Definition stpd2 s m G1 T1 G2 T2 GH := exists n, stp2 s m G1 T1 G2 T2 GH n.

Ltac ep := match goal with
             | [ |- stp2 ?S ?M ?G1 ?T1 ?G2 ?T2 ?GH ?N ] =>
               assert (exists (n:nat), stp2 S M G1 T1 G2 T2 GH n) as EEX
           end.

Ltac eu := match goal with
             | H: stpd2 _ _ _ _ _ _ _ |- _ =>
               destruct H as [? H]
           end.

Global Hint Unfold stpd2 : core.

Lemma stp2_refl_aux: forall n T G GH s,
  closed 0 (length GH) (length G) T ->
  tsize T < n ->
  stpd2 s true G T G T GH.
Proof.
  intros n. induction n; intros; try lia.
  inversion H; subst; eauto; try lia; try simpl in H0.
  - destruct (IHn T1 G GH false) as [n1 IH1]; eauto; try lia.
    destruct (IHn (open (varH (length GH)) T2) G ((true,c1,(G,T1))::GH) false); eauto; try lia.
    simpl. apply closed_open; auto using closed_inc.
    unfold open. rewrite <- open_preserves_size. lia.
    eexists; econstructor; try constructor; eauto.
  - eapply indexr_has in H1. destruct H1 as [[[a c] v] HI].
    eexists; eapply stp2_selx; eauto. 
  - eapply indexr_has in H1. destruct H1 as [[[a c] v] HI].
    eexists; eapply stp2_selax; eauto.
  - destruct (IHn T1 G GH s) as [n1 IH1]; eauto; try lia.
    destruct (IHn T2 G GH s) as [n2 IH2]; eauto; try lia.
    destruct s; eexists; econstructor; try constructor; eauto.
Unshelve. apply 0. apply 0. apply 0. apply 0.
Qed.

Lemma stp2_refl: forall T G GH s,
  closed 0 (length GH) (length G) T ->
  stpd2 s true G T G T GH.
Proof.
  intros. apply stp2_refl_aux with (n:=S (tsize T)); eauto.
Qed.

Lemma concat_same_length: forall {X} (GU: list X) (GL: list X) (GH1: list X) (GH0: list X),
  GU ++ GL = GH1 ++ GH0 ->
  length GU = length GH1 ->
  GU=GH1 /\ GL=GH0.
Proof.
  intros. generalize dependent GH1. induction GU; intros.
  - simpl in H0. induction GH1. rewrite app_nil_l in H. rewrite app_nil_l in H.
    split. reflexivity. apply H.
    simpl in H0. lia.
  - simpl in H0. induction GH1. simpl in H0. lia.
    simpl in H0. inversion H0. simpl in H. inversion H. specialize (IHGU GH1 H4 H2).
    destruct IHGU. subst. split; reflexivity.
Qed.

Lemma concat_same_length': forall {X} (GU: list X) (GL: list X) (GH1: list X) (GH0: list X),
  GU ++ GL = GH1 ++ GH0 ->
  length GL = length GH0 ->
  GU=GH1 /\ GL=GH0.
Proof.
  intros.
  assert (length (GU ++ GL) = length (GH1 ++ GH0)) as A. {
    rewrite H. reflexivity.
  }
  rewrite app_length in A. rewrite app_length in A.
  rewrite H0 in A. apply PeanoNat.Nat.add_cancel_r in A.
  apply concat_same_length; assumption.
Qed.

Lemma exists_GH1L: forall {X} (GU: list X) (GL: list X) (GH1: list X) (GH0: list X) x0,
  length GL = x0 ->
  GU ++ GL = GH1 ++ GH0 ->
  length GH0 <= x0 ->
  exists GH1L, GH1 = GU ++ GH1L /\ GL = GH1L ++ GH0.
Proof.
  intros X GU. induction GU; intros.
  - eexists. rewrite app_nil_l. split. reflexivity. simpl in H0. assumption.
  - induction GH1.

    simpl in H0.
    assert (length (a :: GU ++ GL) = length GH0) as Contra. {
      rewrite H0. reflexivity.
    }
    simpl in Contra. rewrite app_length in Contra. lia.

    simpl in H0. inversion H0.
    specialize (IHGU GL GH1 GH0 x0 H H4 H1).
    destruct IHGU as [GH1L [IHA IHB]].
    exists GH1L. split. simpl. rewrite IHA. reflexivity. apply IHB.
Qed.

Lemma exists_GH0U: forall {X} (GH1: list X) (GH0: list X) (GU: list X) (GL: list X) x0,
  length GL = x0 ->
  GU ++ GL = GH1 ++ GH0 ->
  x0 < length GH0 ->
  exists GH0U, GH0 = GH0U ++ GL.
Proof.
  intros X GH1. induction GH1; intros.
  - simpl in H0. exists GU. symmetry. assumption.
  - induction GU.

    simpl in H0.
    assert (length GL = length (a :: GH1 ++ GH0)) as Contra. {
      rewrite H0. reflexivity.
    }
    simpl in Contra. rewrite app_length in Contra. lia.

    simpl in H0. inversion H0.
    specialize (IHGH1 GH0 GU GL x0 H H4 H1).
    destruct IHGH1 as [GH0U IH].
    exists GH0U. apply IH.
Qed.

Lemma stp_splice : forall GX G0 G1 T1 T2 v1 a c,
   stp GX (G1++G0) T1 T2 ->
   stp GX ((map (spliceb (length G0)) G1) ++ (a,c,v1)::G0)
       (splice (length G0) T1) (splice (length G0) T2).
Proof.
  intros GX G0 G1 T1 T2 v1 a c H. remember (G1++G0) as G.
  revert G0 G1 HeqG.
  induction H; intros; subst GH; simpl; eauto.
  - (* top *)
    eapply stp_top.
    rewrite map_spliceb_length_inc.
    apply closed_splice.
    assumption.
  - (* bot *)
    eapply stp_bot.
    rewrite map_spliceb_length_inc.
    apply closed_splice.
    assumption.
  - (* sel1 *)
    eapply stp_sel1. apply H. assumption.
    assert (splice (length G0) TX=TX) as A. {
      eapply closed_splice_idem. eassumption. lia.
    }
    rewrite <- A. apply IHstp. reflexivity.
  - (* sel2 *)
    eapply stp_sel2. apply H. assumption.
    assert (splice (length G0) TX=TX) as A. {
      eapply closed_splice_idem. eassumption. lia.
    }
    rewrite <- A. apply IHstp. reflexivity.
  - (* sela1 *)
    case_eq (le_lt_dec (length G0) x); intros E LE.
    + eapply stp_sela1.
      apply indexr_spliceb_hi. eauto. eauto.
      eapply closed_splice in H0. assert (S x = x +1) as A by lia.
      rewrite <- A. eapply H0.
      eapply IHstp. eauto.
    + eapply stp_sela1. eapply indexr_spliceb_lo. eauto. eauto. eauto.
      assert (splice (length G0) TX=TX) as A. {
        eapply closed_splice_idem. eassumption. lia.
      }
      rewrite <- A. eapply IHstp. eauto.
  - (* sela2 *)
    case_eq (le_lt_dec (length G0) x); intros E LE.
    + eapply stp_sela2.
      apply indexr_spliceb_hi. eauto. eauto.
      eapply closed_splice in H0. assert (S x = x +1) as A by lia.
      rewrite <- A. eapply H0.
      eapply IHstp. eauto.
    + eapply stp_sela2. eapply indexr_spliceb_lo. eauto. eauto. eauto.
      assert (splice (length G0) TX=TX) as A. {
        eapply closed_splice_idem. eassumption. lia.
      }
      rewrite <- A. eapply IHstp. eauto.
  - (* selax *)
    case_eq (le_lt_dec (length G0) x); intros E LE.
    + eapply stp_selax.
      eapply indexr_spliceb_hi. eassumption. assumption.
    + eapply stp_selax. eapply indexr_spliceb_lo. eauto. eauto.
  - (* all *)
    eapply stp_all. eauto.
    eapply IHstp1. eauto. eauto. eauto.

    simpl. rewrite map_spliceb_length_inc. apply closed_splice. assumption.

    simpl. rewrite map_spliceb_length_inc. apply closed_splice. assumption.

    specialize IHstp2 with (G0:=G0) (G1:=(true,c0,T3) :: G2).
    simpl in IHstp2. rewrite app_length. rewrite map_length. simpl.
    repeat rewrite splice_open_permute with (j:=0). subst x.
    rewrite app_length in IHstp2. simpl in IHstp2.
    eapply IHstp2. eauto.
Qed.

Lemma stp2_splice : forall G1 T1 G2 T2 GH1 GH0 v1 s m n a c,
   stp2 s m G1 T1 G2 T2 (GH1++GH0) n ->
   stp2 s m G1 (splice (length GH0) T1) G2 (splice (length GH0) T2)
        ((map (spliceat (length GH0)) GH1) ++ (a,c,v1)::GH0) n.
Proof.
  intros G1 T1 G2 T2 GH1 GH0 v1 s m n a c H. remember (GH1++GH0) as GH.
  revert GH0 GH1 HeqGH.
  induction H; intros; subst GH; simpl; eauto.
  - (* top *)
    eapply stp2_top.
    rewrite map_spliceat_length_inc.
    apply closed_splice.
    assumption.
  - (* bot *)
    eapply stp2_bot.
    rewrite map_spliceat_length_inc.
    apply closed_splice.
    assumption.
  - (* strong_sel1 *)
    eapply stp2_strong_sel1. apply H. assumption. assumption.
    assert (splice (length GH0) TX=TX) as A. {
      eapply closed_splice_idem. eassumption. lia.
    }
    rewrite <- A. apply IHstp2.
    reflexivity.
  - (* strong_sel2 *)
    eapply stp2_strong_sel2. apply H. assumption. assumption.
    assert (splice (length GH0) TX=TX) as A. {
      eapply closed_splice_idem. eassumption. lia.
    }
    rewrite <- A. apply IHstp2.
    reflexivity.
  - (* sel1 *)
    eapply stp2_sel1. apply H. eassumption. assumption.
    assert (splice (length GH0) TX=TX) as A. {
      eapply closed_splice_idem. eassumption. lia.
    }
    rewrite <- A. apply IHstp2. reflexivity.
  - (* sel2 *)
    eapply stp2_sel2. apply H. eassumption. assumption.
    assert (splice (length GH0) TX=TX) as A. {
      eapply closed_splice_idem. eassumption. lia.
    }
    rewrite <- A. apply IHstp2. reflexivity.
  - (* sela1 *)
    case_eq (le_lt_dec (length GH0) x); intros E LE.
    + eapply stp2_sela1.
      eapply indexr_spliceat_hi. apply H. eauto.
      eapply closed_splice in H0. assert (S x = x + 1) by lia. rewrite <- H2.
      eapply H0.
      eapply IHstp2. eauto.
    + eapply stp2_sela1. eapply indexr_spliceat_lo. apply H. eauto. eauto.
      assert (splice (length GH0) TX=TX) as A. {
        eapply closed_splice_idem. eassumption. lia.
      }
      rewrite <- A. eapply IHstp2. eauto.
  - (* sela2 *)
    case_eq (le_lt_dec (length GH0) x); intros E LE.
    + eapply stp2_sela2.
      eapply indexr_spliceat_hi. apply H. eauto.
      eapply closed_splice in H0. assert (S x = x + 1) by lia. rewrite <- H2.
      eapply H0.
      eapply IHstp2. eauto.
    + eapply stp2_sela2. eapply indexr_spliceat_lo. apply H. eauto. eauto.
      assert (splice (length GH0) TX=TX) as A. {
        eapply closed_splice_idem. eassumption. lia.
      }
      rewrite <- A. eapply IHstp2. eauto.
  - (* selax *)
    case_eq (le_lt_dec (length GH0) x); intros E LE.
    + destruct v as [[? ?] [? ?]]. eapply stp2_selax.
      eapply indexr_spliceat_hi. apply H. eauto.
    + destruct v as [[? ?] [? ?]]. eapply stp2_selax.
      eapply indexr_spliceat_lo. apply H. eauto.
  - (* all *)
    apply stp2_all with (x:= length GH1 + S (length GH0)). eassumption.
    eapply IHstp2_1. reflexivity.

    simpl. rewrite map_spliceat_length_inc. rewrite app_length. lia.
    simpl. rewrite map_spliceat_length_inc. apply closed_splice. assumption.
    simpl. rewrite map_spliceat_length_inc. apply closed_splice. assumption.

    subst x.
    specialize IHstp2_2 with (GH0:=GH0) (GH1:=(true,c0,(G2, T3)) :: GH1).
    simpl in IHstp2_2.
    repeat rewrite splice_open_permute with (j:=0).
    rewrite app_length in IHstp2_2.
    eapply IHstp2_2. reflexivity.
Qed.

Lemma stp_extend : forall G1 GH T1 T2 v1,
                       stp G1 GH T1 T2 ->
                       stp G1 (v1::GH) T1 T2.
Proof.
  intros. induction H; eauto using indexr_extend, closed_inc.
  assert (splice (length GH) T2 = T2) as A2. {
    eapply closed_splice_idem. apply H2. lia.
  }
  assert (splice (length GH) T4 = T4) as A4. {
    eapply closed_splice_idem. apply H3. lia.
  }
  assert (closed 0 (length GH) (length G1) T3). eapply stp_closed1. eauto.
  assert (splice (length GH) T3 = T3) as A3. {
    eapply closed_splice_idem. eauto. lia.
  }
  assert (map (spliceb (length GH)) [(true,c,T3)] ++ v1::GH =
          ((true,c,T3)::v1::GH)) as HGX3. {
    simpl. rewrite A3. eauto.
  }
  apply stp_all with (x:=length (v1 :: GH)). eauto.
  apply IHstp1.
  reflexivity.
  apply closed_inc. apply H2.
  apply closed_inc. apply H3.
  simpl.
  rewrite <- A2. rewrite <- A4.
  unfold open.
  change (varH (S (length GH))) with (varH (0 + (S (length GH)))).
  rewrite -> splice_open_permute. rewrite -> splice_open_permute.
  rewrite <- HGX3. destruct v1. destruct p.
  apply stp_splice.
  simpl. unfold open in H4. rewrite <- H1. apply H4.
Qed.

Lemma stp_extend_mult : forall G T1 T2 GH GH2,
                       stp G GH T1 T2 ->
                       stp G (GH2++GH) T1 T2.
Proof.
  intros. induction GH2.
  - simpl. assumption.
  - simpl.
    apply stp_extend. assumption.
Qed.

Theorem false_beq_nat : forall n m : nat,
     n <> m ->
     beq_nat n m = false.
Proof.
  intros. rewrite <- PeanoNat.Nat.eqb_neq in H. assumption.
Qed.

Lemma indexr_at_index: forall {A} x0 GH0 GH1 (v:A),
  beq_nat x0 (length GH1) = true ->
  indexr x0 (GH0 ++ v :: GH1) = Some v.
Proof.
  intros. apply beq_nat_true in H. subst.
  induction GH0.
  - simpl. rewrite <- beq_nat_refl. reflexivity.
  - simpl.
    rewrite app_length. simpl. rewrite <- plus_n_Sm. rewrite <- plus_Sn_m.
    rewrite false_beq_nat. assumption. lia.
Qed.

Lemma indexr_same: forall {A} x0 (v0:A) GH0 GH1 (v:A) (v':A),
  beq_nat x0 (length GH1) = false ->
  indexr x0 (GH0 ++ v :: GH1) = Some v0 ->
  indexr x0 (GH0 ++ v' :: GH1) = Some v0.
Proof.
  intros ? ? ? ? ? ? ? E H.
  induction GH0.
  - simpl. rewrite E. simpl in H. rewrite E in H. apply H.
  - simpl.
    rewrite app_length. simpl.
    case_eq (beq_nat x0 (length GH0 + S (length GH1))); intros E'.
    simpl in H. rewrite app_length in H. simpl in H. rewrite E' in H.
    rewrite H. reflexivity.
    simpl in H. rewrite app_length in H. simpl in H. rewrite E' in H.
    rewrite IHGH0. reflexivity. assumption.
Qed.

Inductive venv_ext : venv -> venv -> Prop :=
| venv_ext_refl : forall G, venv_ext G G
| venv_ext_cons : forall T G1 G2, venv_ext G1 G2 -> venv_ext (T::G1) G2.

Inductive aenv_ext : aenv -> aenv -> Prop :=
| aenv_ext_nil : aenv_ext nil nil
| aenv_ext_cons :
    forall T G' G A A' a c,
      aenv_ext A' A -> venv_ext G' G ->
      aenv_ext ((a,c,(G',T))::A') ((a,c,(G,T))::A).

Lemma aenv_ext_refl: forall GH, aenv_ext GH GH.
Proof.
  intros. induction GH.
  - apply aenv_ext_nil.
  - destruct a as [[? ?][? ?]]. apply aenv_ext_cons.
    assumption.
    apply venv_ext_refl.
Qed.

Lemma venv_ext__ge_length:
  forall G G',
    venv_ext G' G ->
    length G' >= length G.
Proof.
  intros. induction H; simpl; lia.
Qed.

Lemma aenv_ext__same_length:
  forall GH GH',
    aenv_ext GH' GH ->
    length GH = length GH'.
Proof.
  intros. induction H.
  - simpl. reflexivity.
  - simpl. rewrite IHaenv_ext. reflexivity.
Qed.

Lemma aenv_ext__concat:
  forall GH GH' GU GL,
    aenv_ext GH' GH ->
    GH = GU ++ GL ->
    exists GU' GL', GH' = GU' ++ GL' /\ aenv_ext GU' GU /\ aenv_ext GL' GL.
Proof.
  intros. generalize dependent GU. generalize dependent GL. induction H.
  - intros. symmetry in H0. apply app_eq_nil in H0. destruct H0.
    exists (@nil (bool * class * (venv * ty))). exists (@nil (bool * class * (venv * ty))). simpl. split; eauto. subst. split. apply aenv_ext_refl. apply aenv_ext_refl.
  - intros. induction GU. rewrite app_nil_l in H1. subst.
    exists (@nil (bool * class * (venv * ty))). eexists. rewrite app_nil_l. split. reflexivity.
    split. apply aenv_ext_refl.
    apply aenv_ext_cons. eassumption. eassumption.

    simpl in H1. inversion H1.
    specialize (IHaenv_ext GL GU H4).
    destruct IHaenv_ext as [GU' [GL' [IHA [IHU IHL]]]].
    exists ((a,c,(G', T))::GU'). exists GL'.
    split. simpl. rewrite IHA. reflexivity.
    split. apply aenv_ext_cons. apply IHU. assumption. apply IHL.
Qed.

Lemma indexr_at_ext :
  forall GH GH' x T G a c,
    aenv_ext GH' GH ->
    indexr x GH = Some (a,c,(G, T)) ->
    exists G', indexr x GH' = Some (a,c,(G', T)) /\ venv_ext G' G.
Proof.
  intros GH GH' x T G a c Hext Hindex. induction Hext.
  - simpl in Hindex. inversion Hindex.
  - simpl. simpl in Hindex.
    case_eq (beq_nat x (length A)); intros E.
    rewrite E in Hindex.  inversion Hindex. subst.
    rewrite <- (@aenv_ext__same_length A A'). rewrite E.
    exists G'. split. reflexivity. assumption. assumption.
    rewrite E in Hindex.
    rewrite <- (@aenv_ext__same_length A A'). rewrite E.
    apply IHHext. assumption. assumption.
Qed.

Lemma indexr_extend_venv : forall G G' x T,
                       indexr x G = Some T ->
                       venv_ext G' G ->
                       indexr x G' = Some T.
Proof.
  intros G G' x T H HV.
  induction HV.
  - assumption.
  - apply indexr_extend. apply IHHV. apply H.
Qed.

Lemma stp2_closure_extend_rec:
  forall G1 G2 T1 T2 GH s m n,
    stp2 s m G1 T1 G2 T2 GH n ->
    (forall G1' G2' GH',
       aenv_ext GH' GH ->
       venv_ext G1' G1 ->
       venv_ext G2' G2 ->
       stp2 s m G1' T1 G2' T2 GH' n).
Proof.
  intros G1 G2 T1 T2 GH s m n H.
  induction H; intros; eauto.
  - (* "top" *)
    eapply stp2_top.
    eapply closed_inc_mult; try eassumption; try lia.
    rewrite (@aenv_ext__same_length GH GH'). lia. assumption.
    apply venv_ext__ge_length. assumption.
  - (* "bot" *)
    eapply stp2_bot.
    eapply closed_inc_mult; try eassumption; try lia.
    rewrite (@aenv_ext__same_length GH GH'). lia. assumption.
    apply venv_ext__ge_length. assumption.
  - (* "strong_sel1" *)
    eapply stp2_strong_sel1. eapply indexr_extend_venv. apply H.
    assumption. assumption. assumption.
    apply IHstp2. assumption. apply venv_ext_refl. assumption.
  - (* "strong_sel2" *)
    eapply stp2_strong_sel2. eapply indexr_extend_venv. apply H.
    assumption. assumption. assumption.
    apply IHstp2. assumption. assumption. apply venv_ext_refl.
  - (* "sel1" *)
    eapply stp2_sel1. eapply indexr_extend_venv. apply H.
    assumption. eassumption. assumption.
    apply IHstp2. assumption. apply venv_ext_refl. assumption.
  - (* "sel2" *)
    eapply stp2_sel2. eapply indexr_extend_venv. apply H.
    assumption. eassumption. assumption.
    apply IHstp2. assumption. apply venv_ext_refl. assumption.
  - (* "selx" *)
    eapply stp2_selx.
    eapply indexr_extend_venv. apply H. assumption.
    eapply indexr_extend_venv. apply H0. assumption.
  - (* "sela1" *)
    assert (exists GX', indexr x GH' = Some (a,c,(GX', TX)) /\ venv_ext GX' GX) as A. {
      apply indexr_at_ext with (GH:=GH); assumption.
    }
    inversion A as [GX' [H' HX]].
    apply stp2_sela1 with (GX:=GX') (TX:=TX) (a:=a) (c:=c).
    assumption.
    eapply closed_inc_mult; try eassumption; try lia.
    apply venv_ext__ge_length. assumption.
    apply IHstp2; assumption.
  - (* "sela2" *)
    assert (exists GX', indexr x GH' = Some (a,c,(GX', TX)) /\ venv_ext GX' GX) as A. {
      apply indexr_at_ext with (GH:=GH); assumption.
    }
    inversion A as [GX' [H' HX]].
    apply stp2_sela2 with (GX:=GX') (TX:=TX) (a:=a) (c:=c).
    assumption.
    eapply closed_inc_mult; try eassumption; try lia.
    apply venv_ext__ge_length. assumption.
    apply IHstp2; assumption.
  - (* "selax" *)
    destruct v as [[a c] [GX TX]].
    assert (exists GX', indexr x GH' = Some (a,c,(GX', TX)) /\ venv_ext GX' GX) as A. {
      apply indexr_at_ext with (GH:=GH); assumption.
    }
    inversion A as [GX' [H' HX]].
    apply stp2_selax with (v:=(a,c,(GX',TX))).
    assumption.
  - (* "all" *)
    eapply stp2_all with (x:=length GH'). eauto.
    apply IHstp2_1; assumption.
    reflexivity.
    eapply closed_inc_mult; try eassumption; try lia.
    rewrite (@aenv_ext__same_length GH GH'). lia. assumption.
    apply venv_ext__ge_length. assumption.
    eapply closed_inc_mult; try eassumption; try lia.
    rewrite (@aenv_ext__same_length GH GH'). lia. assumption.
    apply venv_ext__ge_length. assumption.
    subst.  rewrite <- (@aenv_ext__same_length GH GH').
    apply IHstp2_2. apply aenv_ext_cons.
    assumption. assumption. assumption. assumption. assumption.
  - (* "trans" *)
    eapply stp2_transf.
    eapply IHstp2_1.
    assumption. assumption. apply venv_ext_refl.
    eapply IHstp2_2.
    assumption. apply venv_ext_refl. assumption.
Qed.

Lemma stp2_closure_extend : forall G1 T1 G2 T2 GH GX T v s m n a c,
                              stp2 s m G1 T1 G2 T2 ((a,c,(GX,T))::GH) n ->
                              stp2 s m G1 T1 G2 T2 ((a,c,(v::GX,T))::GH) n.
Proof.
  intros. eapply stp2_closure_extend_rec. apply H.
  apply aenv_ext_cons. apply aenv_ext_refl. apply venv_ext_cons.
  apply venv_ext_refl. apply venv_ext_refl. apply venv_ext_refl.
Qed.

Lemma stp2_extend : forall v1 G1 G2 T1 T2 H s m n,
                      stp2 s m G1 T1 G2 T2 H n ->
                       stp2 s m (v1::G1) T1 G2 T2 H n /\
                       stp2 s m G1 T1 (v1::G2) T2 H n /\
                       stp2 s m (v1::G1) T1 (v1::G2) T2 H n.
Proof.
  intros. induction H0;
    try solve [split; try split; intros; eauto using indexr_extend];
    try solve [split; try split; intros; constructor; simpl; eauto using indexr_extend, closed_upgrade_freef];
    try solve [split; try split; intros;
               inversion IHstp2_1 as [? [? ?]]; inversion IHstp2_2 as [? [? ?]]; eauto];
    try solve [split; try split; intros; inversion IHstp2 as [? [? ?]]; eauto];
    try solve [split; try split; intros; inversion IHstp2 as [? [? ?]]; eauto using indexr_extend];
    try solve [split; try split; intros;
               inversion IHstp2_1 as [? [? ?]]; inversion IHstp2_2 as [? [? ?]];
               eauto; eapply stp2_all; simpl; eauto using stp2_closure_extend, closed_upgrade_freef].
Qed.

Lemma stp2_extend2 : forall v1 G1 G2 T1 T2 H s m n,
                       stp2 s m G1 T1 G2 T2 H n ->
                       stp2 s m G1 T1 (v1::G2) T2 H n.
Proof.
  intros. apply (proj2 (stp2_extend v1 G1 G2 T1 T2 H s m n H0)).
Qed.

Lemma stp2_extend1 : forall v1 G1 G2 T1 T2 H s m n,
                       stp2 s m G1 T1 G2 T2 H n ->
                       stp2 s m (v1::G1) T1 G2 T2 H n.
Proof.
  intros. apply (proj1 (stp2_extend v1 G1 G2 T1 T2 H s m n H0)).
Qed.

Lemma stp2_extendH : forall v1 G1 G2 T1 T2 GH s m n,
                       stp2 s m G1 T1 G2 T2 GH n ->
                       stp2 s m G1 T1 G2 T2 (v1::GH) n.
Proof.
  intros.
  induction H;
    try solve [try constructor; simpl; eauto using indexr_extend, closed_upgrade_free];
    try solve [eapply stp2_transf; simpl; eauto].
  assert (splice (length GH) T2 = T2) as A2. {
    eapply closed_splice_idem. apply H2. lia.
  }
  assert (splice (length GH) T4 = T4) as A4. {
    eapply closed_splice_idem. apply H3. lia.
  }
  assert (closed 0 (length GH) (length G2) T3). eapply stp2_closed1. eauto.
  assert (splice (length GH) T3 = T3) as A3. {
    eapply closed_splice_idem. eauto. lia.
  }
  assert (map (spliceat (length GH)) [(true,c,(G2, T3))] ++ v1::GH =
          ((true,c,(G2, T3))::v1::GH)) as HGX3. {
    simpl. rewrite A3. eauto.
  }
  eapply stp2_all. eauto.
  apply IHstp2_1.
  reflexivity.
  apply closed_inc. apply H2.
  apply closed_inc. apply H3.
  simpl.
  rewrite <- A2. rewrite <- A4.
  unfold open.
  change (varH (S (length GH))) with (varH (0 + (S (length GH)))).
  rewrite -> splice_open_permute.
  rewrite -> splice_open_permute.
  rewrite <- HGX3.
  destruct v1 as [[? ?][? ?]].
  apply stp2_splice.
  subst x. simpl. unfold open in H4. apply H4.
Qed.

Lemma stp2_extendH_mult : forall G1 G2 T1 T2 H H2 s m n,
                       stp2 s m G1 T1 G2 T2 H n ->
                       stp2 s m G1 T1 G2 T2 (H2++H) n.
Proof.
  intros. induction H2.
  - simpl. assumption.
  - simpl.
    apply stp2_extendH. assumption.
Qed.

Lemma stp2_extendH_mult0 : forall G1 G2 T1 T2 H2 s m n,
                       stp2 s m G1 T1 G2 T2 [] n ->
                       stp2 s m G1 T1 G2 T2 H2 n.
Proof.
  intros.
  assert (H2 = H2++[]) as A by apply app_nil_end. rewrite A.
  apply stp2_extendH_mult. assumption.
Qed.

Lemma stp2_reg  : forall G1 G2 T1 T2 GH s m n,
                    stp2 s m G1 T1 G2 T2 GH n ->
                    stpd2 s true G1 T1 G1 T1 GH /\ stpd2 s true G2 T2 G2 T2 GH.
Proof.
  intros.
  apply stp2_closed in H. destruct H as [H1 H2].
  split; apply stp2_refl; assumption.
Qed.

Lemma stp2_reg2 : forall G1 G2 T1 T2 GH s m n,
                       stp2 s m G1 T1 G2 T2 GH n ->
                       stpd2 s true G2 T2 G2 T2 GH.
Proof.
  intros. apply (proj2 (stp2_reg G1 G2 T1 T2 GH s m n H)).
Qed.

Lemma stp2_reg1 : forall G1 G2 T1 T2 GH s m n,
                       stp2 s m G1 T1 G2 T2 GH n ->
                       stpd2 s true G1 T1 G1 T1 GH.
Proof.
  intros. apply (proj1 (stp2_reg G1 G2 T1 T2 GH s m n H)).
Qed.

Lemma stp_reg  : forall G GH T1 T2,
                    stp G GH T1 T2 ->
                    stp G GH T1 T1 /\ stp G GH T2 T2.
Proof.
  intros.
  apply stp_closed in H. destruct H as [H1 H2].
  split; apply stp_refl; assumption.
Qed.

Lemma stp_reg2 : forall G GH T1 T2,
                       stp G GH T1 T2 ->
                       stp G GH T2 T2.
Proof.
  intros. apply (proj2 (stp_reg G GH T1 T2 H)).
Qed.

Lemma stp_reg1 : forall G GH T1 T2,
                       stp G GH T1 T2 ->
                       stp G GH T1 T1.
Proof.
  intros. apply (proj1 (stp_reg G GH T1 T2 H)).
Qed.

Lemma stpd2_extend2 : forall v1 G1 G2 T1 T2 H s m,
                       stpd2 s m G1 T1 G2 T2 H ->
                       stpd2 s m G1 T1 (v1::G2) T2 H.
Proof.
  intros. destruct H0 as [n Hsub]. eexists n.
  apply stp2_extend2; eauto.
Qed.

Lemma stpd2_extend1 : forall v1 G1 G2 T1 T2 H s m,
                       stpd2 s m G1 T1 G2 T2 H ->
                       stpd2 s m (v1::G1) T1 G2 T2 H.
Proof.
  intros. destruct H0 as [n Hsub]. eexists n.
  apply stp2_extend1; eauto.
Qed.

Lemma stpd2_extendH : forall v1 G1 G2 T1 T2 GH s m,
                       stpd2 s m G1 T1 G2 T2 GH ->
                       stpd2 s m G1 T1 G2 T2 (v1::GH).
Proof.
  intros. destruct H as [n Hsub]. exists n.
  apply stp2_extendH; eauto.
Qed.

Lemma stpd2_extendH_mult : forall G1 G2 T1 T2 GH GH2 s m,
                       stpd2 s m G1 T1 G2 T2 GH ->
                       stpd2 s m G1 T1 G2 T2 (GH2++GH).
Proof.
  intros. destruct H as [n Hsub]. exists n.
  apply stp2_extendH_mult; eauto.
Qed.

Lemma stpd2_closed2 : forall G1 G2 T1 T2 GH s m,
                       stpd2 s m G1 T1 G2 T2 GH ->
                       closed 0 (length GH) (length G2) T2.
Proof.
  intros. destruct H as [n Hsub].
  eapply stp2_closed2; eauto.
Qed.

Lemma stpd2_closed1 : forall G1 G2 T1 T2 GH s m,
                       stpd2 s m G1 T1 G2 T2 GH ->
                       closed 0 (length GH) (length G1) T1.
Proof.
  intros. destruct H as [n Hsub].
  eapply stp2_closed1; eauto.
Qed.

Lemma valtp_extend : forall vs v v1 T,
                       val_type vs v T ->
                       val_type (v1::vs) v T.
Proof.
  intros. induction H; eauto; econstructor; eauto; eapply stpd2_extend2; eauto.
Qed.

Lemma indexr_safe_ex: forall H1 G1 TF i a c,
             wf_env H1 G1 ->
             indexr i G1 = Some (a,c,TF) ->
             exists v, indexr i H1 = Some (a,c,v) /\ val_type H1 v TF.
Proof. intros. induction H.
   - (* "nil" *) inversion H0.
   - (* "cons" *) inversion H0.
     case_eq (beq_nat i (length ts)); intros E2.
     * (* "hit" *)
       rewrite E2 in H3. inversion H3. subst. clear H3.
       assert (length ts = length vs). symmetry. eapply wf_length. eauto.
       simpl. rewrite H2 in E2. rewrite E2.
       eexists. split. eauto. assumption.
     * (* "miss" *)
       rewrite E2 in H3.
       assert (exists v0,
                 indexr i vs = Some (a,c,v0) /\ val_type vs v0 TF). eauto.
       destruct H2. destruct H2.
       eexists. split. eapply indexr_extend. eauto.
       eapply valtp_extend. assumption.
Qed.

Lemma index_safeh_ex: forall H1 H2 G1 GH TF i a c,
             wf_env H1 G1 -> wf_envh H1 H2 GH ->
             indexr i GH = Some (a,c,TF) ->
             exists v, indexr i H2 = Some (a,c,v) /\ valh_type H1 H2 v TF.
Proof. intros. induction H0.
   - (* "nil" *) inversion H3.
   - (* "cons" *) inversion H3.
     case_eq (beq_nat i (length ts)); intros E2.
     * (* "hit" *)
       rewrite E2 in H2. inversion H2. subst. clear H2.
       assert (length ts = length vs). symmetry. eapply wfh_length. eauto.
       simpl. rewrite H1 in E2. rewrite E2.
       eexists. split. eauto. econstructor.
     * (* "miss" *)
       rewrite E2 in H2.
       assert (exists v : venv * ty,
                 indexr i vs = Some (a,c,v) /\ valh_type vvs vs v TF). eauto.
       destruct H1. destruct H1.
       eexists. split. eapply indexr_extend. eauto.
       inversion H4. subst.
       eapply v_tya. (* aenv is not constrained -- bit of a cheat?*)
Qed.

Inductive res_type: venv -> option vl -> ty -> Prop :=
| not_stuck: forall venv v T,
      val_type venv v T ->
      res_type venv (Some v) T.

Global Hint Constructors res_type : core.
Global Hint Resolve not_stuck : core.

(* ### Transitivity ### *)

Lemma stpd2_top: forall G1 G2 GH T s,
    closed 0 (length GH) (length G1) T ->
    stpd2 s true G1 T G2 TTop GH.
Proof. intros. exists (S 0). eauto. Qed.
Lemma stpd2_bot: forall G1 G2 GH T s,
    closed 0 (length GH) (length G2) T ->
    stpd2 s true G1 TBot G2 T GH.
Proof. intros. exists (S 0). eauto. Qed.
Lemma stpd2_mem: forall G1 G2 S1 U1 S2 U2 GH s,
    stpd2 s s G1 U1 G2 U2 GH ->
    stpd2 s false G2 S2 G1 S1 GH ->
    stpd2 s true G1 (TMem S1 U1) G2 (TMem S2 U2) GH.
Proof. intros. repeat eu. eauto. Qed.
Lemma stpd2_strong_sel1: forall G1 G2 GX TX x T2 GH a c,
    indexr x G1 = Some (a,c,(vty GX TX)) ->
    val_type GX (vty GX TX) (TMem TX TX) -> (* for downgrade *)
    closed 0 0 (length GX) TX ->
    stpd2 true true GX TX G2 T2 GH ->
    stpd2 true true G1 (TSel (varF x)) G2 T2 GH.
Proof. intros. repeat eu. eauto. Qed.
Lemma stpd2_strong_sel2: forall G1 G2 GX TX x T1 GH a c,
    indexr x G2 = Some (a,c,(vty GX TX)) ->
    val_type GX (vty GX TX) (TMem TX TX) -> (* for downgrade *)
    closed 0 0 (length GX) TX ->
    stpd2 true false G1 T1 GX TX GH ->
    stpd2 true true G1 T1 G2 (TSel (varF x)) GH.
Proof. intros. repeat eu. eauto. Qed.
Lemma stpd2_sel1: forall G1 G2 v TX x T2 GH a c,
    indexr x G1 = Some (a,c,v) ->
    val_type (base v) v TX ->
    closed 0 0 (length (base v)) TX ->
    stpd2 false false (base v) TX G2 (TMem TBot T2) GH ->
    stpd2 false true G1 (TSel (varF x)) G2 T2 GH.
Proof. intros. repeat eu. eauto. Qed.
Lemma stpd2_sel2: forall G1 G2 v TX x T1 GH a c,
    indexr x G2 = Some (a,c,v) ->
    val_type (base v) v TX ->
    closed 0 0 (length (base v)) TX ->
    stpd2 false false (base v) TX G1 (TMem T1 TTop) GH ->
    stpd2 false true G1 T1 G2 (TSel (varF x)) GH.
Proof. intros. repeat eu. eauto. Qed.
Lemma stpd2_selx: forall G1 G2 v x1 x2 GH s a1 c1 a2 c2,
    indexr x1 G1 = Some (a1,c1,v) ->
    indexr x2 G2 = Some (a2,c2,v) ->
    stpd2 s true G1 (TSel (varF x1)) G2 (TSel (varF x2)) GH.
Proof. intros. exists (S 0). eauto. Qed.
Lemma stpd2_sela1: forall G1 G2 GX TX x T2 GH a c,
    indexr x GH = Some (a,c,(GX, TX)) ->
    closed 0 x (length GX) TX ->
    stpd2 false false GX TX G2 (TMem TBot T2) GH ->
    stpd2 false true G1 (TSel (varH x)) G2 T2 GH.
Proof. intros. repeat eu. eauto. Qed.
Lemma stpd2_sela2: forall G1 G2 GX T1 TX x GH a c,
    indexr x GH = Some (a,c,(GX, TX)) ->
    closed 0 x (length GX) TX ->
    stpd2 false false GX TX G1 (TMem T1 TTop) GH ->
    stpd2 false true G1 T1 G2 (TSel (varH x)) GH.
Proof. intros. repeat eu. eauto. Qed.
Lemma stpd2_selax: forall G1 G2 v x GH s,
    indexr x GH = Some v ->
    stpd2 s true G1 (TSel (varH x)) G2 (TSel (varH x)) GH.
Proof. intros. exists (S 0). eauto. Qed.
Lemma stpd2_all: forall G1 G2 T1 T2 T3 T4 x GH s c c2 c4,
    subcl c2 c4 ->
    stpd2 false false G2 T3 G1 T1 GH ->
    x = length GH ->
    closed 1 (length GH) (length G1) T2 ->
    closed 1 (length GH) (length G2) T4 ->
    stpd2 false false G1 (open (varH x) T2) G2 (open (varH x) T4) ((true,c,(G2, T3))::GH) ->
    stpd2 s true G1 (TAll T1 c T2 c2) G2 (TAll T3 c T4 c4) GH.
Proof. intros. repeat eu. eauto. Qed.
Lemma stpd2_wrapf: forall G1 G2 T1 T2 GH s,
    stpd2 s true G1 T1 G2 T2 GH ->
    stpd2 s false G1 T1 G2 T2 GH.
Proof. intros. repeat eu. eauto. Qed.
Lemma stpd2_transf: forall G1 G2 G3 T1 T2 T3 GH s,
    stpd2 s true G1 T1 G2 T2 GH ->
    stpd2 s false G2 T2 G3 T3 GH ->
    stpd2 s false G1 T1 G3 T3 GH.
Proof. intros. repeat eu. eauto. Qed.

Lemma stpd2_trans_aux: forall n, forall G1 G2 G3 T1 T2 T3 H s n1,
  stp2 s false G1 T1 G2 T2 H n1 -> n1 < n ->
  stpd2 s false G2 T2 G3 T3 H ->
  stpd2 s false G1 T1 G3 T3 H.
Proof.
  intros n. induction n; intros; try lia; repeat eu; subst; inversion H0.
  - (* "wrapf" *) eapply stpd2_transf; eauto.
  - (* "transf" *) eapply stpd2_transf. eauto. eapply IHn. eauto. lia. eauto.
Qed.

Lemma stpd2_trans: forall G1 G2 G3 T1 T2 T3 H s,
  stpd2 s false G1 T1 G2 T2 H ->
  stpd2 s false G2 T2 G3 T3 H ->
  stpd2 s false G1 T1 G3 T3 H.
Proof. intros. repeat eu. eapply stpd2_trans_aux; eauto. Qed.

Lemma stp2_narrow_aux: forall n, forall m G1 T1 G2 T2 GH n0,
  stp2 false m G1 T1 G2 T2 GH n0 ->
  n0 <= n ->
  forall GH1 GH0 GH' GX1 TX1 GX2 TX2 aa cc2 cc1,
    GH=GH1++[(aa,cc2,(GX2,TX2))]++GH0 ->
    GH'=GH1++[(aa,cc1,(GX1,TX1))]++GH0 ->
    stpd2 false false GX1 TX1 GX2 TX2 GH0 ->
    stpd2 false m G1 T1 G2 T2 GH'.
Proof.
  intros n.
  induction n.
  - (* "z" *) intros. inversion H0. subst. inversion H; eauto.
  - (* "s" *) intros m G1 T1 G2 T2 GH n0 H NE. inversion H; subst;
    intros GH1 GH0 GH' GX1 TX1 GX2 TX2 aa cc2 cc1 EGH EGH' HX; eauto.
    + (* "top" *) eapply stpd2_top.
      subst. rewrite app_length. simpl. rewrite app_length in H0. simpl in H0. apply H0.
    + (* "bot" *) eapply stpd2_bot.
      subst. rewrite app_length. simpl. rewrite app_length in H0. simpl in H0. apply H0.
    + (* "mem_true" *) eapply stpd2_mem.
      eapply IHn; try eassumption. lia.
      eapply IHn; try eassumption. lia.
    + (* "sel1" *) eapply stpd2_sel1; try eassumption.
      eapply IHn; try eassumption. lia.
    + (* "sel2" *) eapply stpd2_sel2; try eassumption.
      eapply IHn; try eassumption. lia.
    + (* "sela1" *)
      unfold id,venv,aenv in *.
      case_eq (beq_nat x (length GH0)); intros E.
      * assert (indexr x ([(aa,cc2,(GX2, TX2))]++GH0) = Some (aa,cc2,(GX2, TX2))) as A2. {
          simpl. rewrite E. reflexivity.
        }
        assert (indexr x GH = Some (aa,cc2,(GX2, TX2))) as A2'. {
          rewrite EGH. eapply indexr_extend_mult. apply A2.
        }
        unfold venv in A2'. unfold env in A2'. rewrite A2' in H0. inversion H0. subst.
        inversion HX as [nx HX'].
        eapply stpd2_sela1.
        eapply indexr_extend_mult. simpl. unfold env in E. rewrite E. reflexivity.
        apply beq_nat_true in E. rewrite E. eapply stp2_closed1. eassumption.
        eapply stpd2_trans.
        eexists. eapply stp2_extendH_mult. eapply stp2_extendH_mult. eassumption.
        eapply IHn; try eassumption. lia.
        reflexivity. reflexivity.
      * assert (indexr x GH' = Some (a,c,(GX, TX))) as A. {
          subst.
          eapply indexr_same. apply E. eassumption.
        }
        eapply stpd2_sela1. eapply A. assumption.
        eapply IHn; try eassumption. lia.
    + (* "sela2" *)
      unfold id,venv,aenv in *.
      case_eq (beq_nat x (length GH0)); intros E.
      * assert (indexr x ([(aa,cc2,(GX2, TX2))]++GH0) = Some (aa,cc2,(GX2, TX2))) as A2. {
          simpl. rewrite E. reflexivity.
        }
        assert (indexr x GH = Some (aa,cc2,(GX2, TX2))) as A2'. {
          rewrite EGH. eapply indexr_extend_mult. apply A2.
        }
        unfold venv in A2'. unfold env in A2'. rewrite A2' in H0. inversion H0. subst.
        inversion HX as [nx HX'].
        eapply stpd2_sela2.
        eapply indexr_extend_mult. simpl. unfold env in E. rewrite E. reflexivity.
        apply beq_nat_true in E. rewrite E. eapply stp2_closed1. eassumption.
        eapply stpd2_trans.
        eexists. eapply stp2_extendH_mult. eapply stp2_extendH_mult. eassumption.
        eapply IHn; try eassumption. lia.
        reflexivity. reflexivity.
      * assert (indexr x GH' = Some (a,c,(GX, TX))) as A. {
          subst.
          eapply indexr_same. apply E. eassumption.
        }
        eapply stpd2_sela2. eapply A. assumption.
        eapply IHn; try eassumption. lia.
    + (* "selax" *)
      unfold id,venv,aenv in *.
      case_eq (beq_nat x (length GH0)); intros E.
      * assert (indexr x ([(aa,cc2,(GX2, TX2))]++GH0) = Some (aa,cc2,(GX2, TX2))) as A2. {
          simpl. rewrite E. reflexivity.
        }
        assert (indexr x GH = Some (aa,cc2,(GX2, TX2))) as A2'. {
          rewrite EGH. eapply indexr_extend_mult. apply A2.
        }
        unfold venv in A2'. rewrite A2' in H0. inversion H0. subst.
        inversion HX as [nx HX'].
        eapply stpd2_selax.
        eapply indexr_extend_mult. simpl. unfold id,venv,aenv in *. rewrite E.
        reflexivity.
      * assert (indexr x GH' = Some v) as A. {
          subst.
          eapply indexr_same. apply E. eassumption.
        }
        eapply stpd2_selax. eapply A.
    + (* "all" *)
      assert (length GH = length GH') as A. {
        subst. clear.
        induction GH1.
        - simpl. reflexivity.
        - simpl. simpl in IHGH1. rewrite IHGH1. reflexivity.
      }
      eapply stpd2_all. eauto. eauto.
      eapply IHn; try eassumption. lia.
      rewrite <- A. reflexivity.
      rewrite <- A. assumption. rewrite <- A. assumption.
      subst.
      eapply IHn with (GH1:=(true,c,(G2, T4)) :: GH1); try eassumption. lia.
      simpl. reflexivity. simpl. reflexivity.
    + (* "wrapf" *)
      eapply stpd2_wrapf.
      eapply IHn; try eassumption. lia.
    + (* "transf" *)
      eapply stpd2_transf.
      eapply IHn; try eassumption. lia.
      eapply IHn; try eassumption. lia.
Unshelve. apply 0.
Qed.

Lemma stpd2_narrow: forall G1 G2 G3 G4 T1 T2 T3 T4 H a c2 c1,
  stpd2 false false G1 T1 G2 T2 H -> (* careful about H! *)
  stpd2 false false G3 T3 G4 T4 ((a,c2,(G2,T2))::H) ->
  stpd2 false false G3 T3 G4 T4 ((a,c1,(G1,T1))::H).
Proof.
  intros. inversion H1 as [n H'].
  eapply (stp2_narrow_aux n) with (GH1:=[]) (GH0:=H). eapply H'. lia.
  simpl. reflexivity. reflexivity.
  assumption.
Qed.

Ltac indexr_contra :=
  match goal with
    | H: indexr ?N [] = Some ?V |- _ => simpl in H; inversion H
  end.

Lemma stpd2_untrans_aux: forall n, forall m G1 G2 G3 T1 T2 T3 GH n1,
  stp2 true m G1 T1 G2 T2 GH n1 -> n1 < n ->
  stpd2 true true G2 T2 G3 T3 GH ->
  stpd2 true true G1 T1 G3 T3 GH.
Proof.
  intros n. induction n; intros; try lia. eu.
  inversion H; subst;
  try solve [inversion H1; eexists; eauto];
  try solve [eapply stpd2_bot; eauto using stp2_closed2];
  try solve [eapply stpd2_strong_sel1; eauto; eapply IHn; eauto; try lia];
  try solve [eapply IHn; [eapply H2 | lia | eauto]]; (* wrapf *)
  try solve [eapply IHn; [eapply H2 | lia | (eapply IHn; [ eapply H3 | lia | eauto ])]]; (* transf *)
  inversion H1; subst;
  try solve [eapply stpd2_top; eauto using stp2_closed1];
  try solve [eapply stpd2_strong_sel2; eauto];
  try solve [eapply stpd2_mem; [eapply IHn; eauto; try lia |
                                eapply stpd2_trans; eauto]];
  try solve [eapply stpd2_sela1; eauto; eapply stpd2_wrapf; eapply IHn; eauto; try lia];
  try solve [indexr_contra].
  - (* "sel2 - sel1" *)
    rewrite H7 in H2. inversion H2. subst.
    eapply IHn. eapply H5. lia. eauto.
  - (* "sel2 - selx" *)
    rewrite H7 in H2. inversion H2. subst.
    eapply stpd2_strong_sel2; eauto.
  - (* "selx - sel1" *)
    rewrite H5 in H3. inversion H3. subst.
    eapply stpd2_strong_sel1; eauto.
  - (* "selx - selx" *)
    rewrite H5 in H3. inversion H3. subst.
    eapply stpd2_selx; eauto.
  - (* "selax - selax" *)
    eapply stpd2_selax; eauto.
  - (* "all - all" *)
    eapply stpd2_all; eauto. eapply subcl_trans. eassumption. eassumption.
    eapply stpd2_trans; eauto.
    eapply stpd2_trans. eapply stpd2_narrow. eexists. eapply H12. unfold stpd2. eexists. eauto. eauto.
Unshelve. apply 0.
Qed.

(* We don't generally need to push back transitivity in non-empty abstract contexts. *)
Lemma stpd2_strong_trans: forall G1 G2 G3 T1 T2 T3,
  stpd2 true true G1 T1 G2 T2 [] ->
  stpd2 true true G2 T2 G3 T3 [] ->
  stpd2 true true G1 T1 G3 T3 [].
Proof. intros. repeat eu. eapply stpd2_untrans_aux; eauto. Qed.

Lemma stpd2_strong_untrans: forall G1 G2 T1 T2,
  stpd2 true false G1 T1 G2 T2 [] ->
  stpd2 true true G1 T1 G2 T2 [].
Proof.
  intros. destruct H as [n H].
  eapply stpd2_untrans_aux; eauto using stp2_reg2.
Qed.

Lemma valtp_widen: forall vf H1 H2 T1 T2,
  val_type H1 vf T1 ->
  stpd2 true true H1 T1 H2 T2 [] ->
  val_type H2 vf T2.
Proof.
  intros. inversion H; subst; econstructor; eauto; eapply stpd2_strong_trans; eauto.
Qed.

Lemma restp_widen: forall vf H1 H2 T1 T2,
  res_type H1 vf T1 ->
  stpd2 true true H1 T1 H2 T2 [] ->
  res_type H2 vf T2.
Proof.
  intros. inversion H. eapply not_stuck. eapply valtp_widen; eauto.
Qed.

Lemma invert_typ: forall venv vx S U,
  val_type venv vx (TMem S U) ->
  exists GX TX,
    vx = (vty GX TX) /\
    stpd2 true false venv S GX TX [] /\
    stpd2 true true GX TX venv U [].
Proof.
  intros. inversion H; ev; tryfalse_invert; inversion H1; subst;
  repeat eexists; eauto.
Qed.

Lemma stpd2_to_strong_aux: forall n, forall G1 G2 T1 T2 m n1,
  stp2 false m G1 T1 G2 T2 [] n1 -> n1 < n ->
  stpd2 true m G1 T1 G2 T2 [].
Proof.
  intros n. induction n; intros; try lia.
  inversion H; subst; try solve [inversion H1].
  - (* "top" *)
    eapply stpd2_top; eauto.
  - (* "bot" *)
    eapply stpd2_bot; eauto.
  - (* "mem" *)
    eapply stpd2_mem; auto.
    eapply stpd2_strong_untrans. eapply IHn; eauto. lia.
    eapply IHn; eauto. lia.
  - (* "sel1" *)
    eapply IHn in H4. eapply stpd2_strong_untrans in H4.
    eapply valtp_widen with (2:=H4) in H2.
    remember H2 as Hv. clear HeqHv.
    eapply invert_typ in H2. ev. subst.
    assert (closed 0 (length ([]:aenv)) (length x0) x1). eapply stpd2_closed1; eauto.
    eapply stpd2_strong_sel1. eauto. eauto.
    inversion Hv; subst.
    eapply v_ty. eassumption. eapply stp2_refl. eauto. eauto.
    eassumption. lia.
  - (* "sel2" *)
    eapply IHn in H4. eapply stpd2_strong_untrans in H4.
    eapply valtp_widen with (2:=H4) in H2.
    remember H2 as Hv. clear HeqHv.
    eapply invert_typ in H2. ev. subst.
    assert (closed 0 (length ([]:aenv)) (length x0) x1). eapply stpd2_closed1; eauto.
    eapply stpd2_strong_sel2. eauto. eauto.
    inversion Hv; subst.
    eapply v_ty. eassumption. eapply stp2_refl. eauto. eauto.
    eassumption. lia.
  - (* "selx" *)
    eapply stpd2_selx; eauto.
  - (* "all" *)
    eapply stpd2_all; eauto.
  - (* "wrapf" *)
    eapply stpd2_wrapf; eauto.
    eapply IHn; eauto. lia.
  - (* "transf" *)
    eapply stpd2_transf.
    eapply IHn; eauto. lia.
    eapply IHn; eauto. lia.
Qed.

Lemma stpd2_to_strong: forall G1 G2 T1 T2 m,
  stpd2 false m G1 T1 G2 T2 [] ->
  stpd2 true m G1 T1 G2 T2 [].
Proof. intros. repeat eu. eapply stpd2_to_strong_aux; eauto. Qed.

Lemma stpd2_upgrade: forall G1 G2 T1 T2,
  stpd2 false false G1 T1 G2 T2 nil ->
  stpd2 true true G1 T1 G2 T2 nil.
Proof.
  intros.
  eapply stpd2_strong_untrans. eapply stpd2_to_strong. eauto.
Qed.

Lemma stpd2_downgrade_aux: forall G1 G2 T1 T2 H m,
  stpd2 true m G1 T1 G2 T2 H ->
  stpd2 false m G1 T1 G2 T2 H.
Proof.
  intros. inversion H0. dependent induction H1; try solve [eexists; eauto].
  - (* "mem" *)
    eapply stpd2_mem. eapply stpd2_wrapf. eapply IHstp2_1. eexists. eassumption. reflexivity.
    eapply IHstp2_2. eexists. eassumption. reflexivity.
  - (* "sel1" *)
    eapply stpd2_sel1; eauto. simpl.
    eapply stpd2_wrapf. eapply stpd2_mem.
    eapply stpd2_wrapf. eapply IHstp2. eexists. eassumption. reflexivity.
    eapply stpd2_wrapf. eapply stpd2_bot.
    eapply closed_upgrade_free. eassumption. lia.
  - (* "sel2" *)
    eapply stpd2_sel2; eauto. simpl.
    eapply stpd2_wrapf. eapply stpd2_mem.
    eapply stpd2_wrapf. eapply stpd2_top.
    simpl. eapply closed_upgrade_free. eassumption. lia.
    eapply IHstp2. eexists. eassumption. reflexivity.
  - (* "wrap" *)
    eapply stpd2_wrapf. eapply IHstp2. eexists. eassumption. reflexivity.
  - (* "trans" *)
    eapply stpd2_transf.
    eapply IHstp2_1. eexists. eassumption. reflexivity.
    eapply IHstp2_2. eexists. eassumption. reflexivity.
  Unshelve.
  apply 0. apply 0. apply 0. apply 0.
Qed.

Lemma stpd2_downgrade: forall G1 G2 T1 T2 H,
  stpd2 true true G1 T1 G2 T2 H ->
  stpd2 false false G1 T1 G2 T2 H.
Proof.
  intros. eapply stpd2_downgrade_aux. eapply stpd2_wrapf. assumption.
Qed.

(* ### Substitution for relating static and dynamic semantics ### *)
Lemma indexr_hit2 {X}: forall x (B:X) A G,
  length G = x ->
  B = A ->
  indexr x (B::G) = Some A.
Proof.
  intros.
  unfold indexr.
  assert (beq_nat x (length G) = true). eapply beq_nat_true_iff. eauto.
  rewrite H1. subst. reflexivity.
Qed.

Lemma indexr_miss {X}: forall x (B:X) A G,
  indexr x (B::G) = A ->
  x <> (length G)  ->
  indexr x G = A.
Proof.
  intros.
  unfold indexr in H.
  assert (beq_nat x (length G) = false). eapply beq_nat_false_iff. eauto.
  rewrite H1 in H. eauto.
Qed.

Lemma indexr_hit {X}: forall x (B:X) A G,
  indexr x (B::G) = Some A ->
  x = length G ->
  B = A.
Proof.
  intros.
  unfold indexr in H.
  assert (beq_nat x (length G) = true). eapply beq_nat_true_iff. eauto.
  rewrite H1 in H. inversion H. eauto.
Qed.

Lemma indexr_hit0: forall GH (GX0:venv) (TX0:ty) (a:bool) (c:class),
      indexr 0 (GH ++ [(a,c,(GX0, TX0))]) =
      Some (a,c,(GX0, TX0)).
Proof.
  intros GH. induction GH.
  - intros. simpl. eauto.
  - intros. simpl. destruct a. simpl. rewrite app_length. simpl.
    assert (length GH + 1 = S (length GH)). lia. rewrite H.
    eauto.
Qed.

Global Hint Resolve beq_nat_true_iff : core.
Global Hint Resolve beq_nat_false_iff : core.

Lemma closed_no_open: forall T x i j k,
  closed i j k T ->
  T = open_rec i x T.
Proof.
  intros. induction H; intros; eauto;
  try solve [compute; compute in IHclosed; rewrite <-IHclosed; auto];
  try solve [compute; compute in IHclosed1; compute in IHclosed2;
             rewrite <-IHclosed1; rewrite <-IHclosed2; auto].

  (* "TVarB" *)
    unfold open_rec. assert (i <> x0). lia.
    apply beq_nat_false_iff in H0.
    rewrite H0. auto.
Qed.

Lemma open_subst_commute: forall T2 V j k x i,
closed i j k (TSel V) ->
(open_rec i (varH x) (subst V T2)) =
(subst V (open_rec i (varH (x+1)) T2)).
Proof.
  intros T2 TX j k. induction T2; intros; eauto; try destruct v; eauto.
  - simpl. rewrite IHT2_1; eauto. rewrite IHT2_2; eauto.
    eapply closed_upgrade. eauto. eauto.
  - simpl.
    case_eq (beq_nat i 0); intros E.
    apply beq_nat_true in E. subst.
    case_eq (beq_nat i0 0); intros E0.
    apply beq_nat_true in E0. subst.
    destruct TX; eauto.
    simpl. destruct i; eauto.
    inversion H; subst. lia.
    simpl. reflexivity.
    case_eq (beq_nat i0 0); intros E0.
    apply beq_nat_true in E0. subst.
    simpl. destruct TX; eauto.
    case_eq (beq_nat i i0); intros E1.
    apply beq_nat_true in E1. subst.
    inversion H; subst. lia.
    reflexivity.
    simpl. reflexivity.
  - simpl.
    case_eq (beq_nat i i0); intros E.
    apply beq_nat_true in E; subst.
    simpl.
    assert (x+1 <> 0) as A by lia.
    eapply beq_nat_false_iff in A.
    rewrite A.
    assert (x = x + 1 - 1) as B. unfold id. lia.
    rewrite <- B. reflexivity.
    simpl. reflexivity.
  - simpl. rewrite IHT2_1. rewrite IHT2_2. eauto. eauto. eauto.
Qed.

Lemma closed_no_subst: forall T i k TX,
   closed i 0 k T ->
   subst TX T = T.
Proof.
  intros T. induction T; intros; inversion H; simpl; eauto;
  try solve [rewrite (IHT i k TX); eauto; try lia];
  try solve [rewrite (IHT1 i k TX); eauto; rewrite (IHT2 (S i) k TX); eauto; try lia];
  try solve [rewrite (IHT1 i k TX); eauto; rewrite (IHT2 i k TX); eauto; try lia];
  try lia.
Qed.

Lemma closed_subst: forall i j k V T, closed i (j+1) k T -> closed 0 j k (TSel V) -> closed i j k (subst V T).
Proof.
  intros. generalize dependent i.
  induction T; intros; inversion H;
  try econstructor;
  try eapply IHT1; eauto; try eapply IHT2; eauto; try eapply IHT; eauto.

  - (* "TVarH" *) simpl.
    case_eq (beq_nat x 0); intros E.
    eapply closed_upgrade. eapply closed_upgrade_free.
    eauto. lia. eauto. lia.
    econstructor. assert (x > 0). eapply beq_nat_false_iff in E. lia. lia.
Qed.

Lemma closed_nosubst: forall i j k V T, closed i (j+1) k T -> nosubst T -> closed i j k (subst V T).
Proof.
  intros. generalize dependent i.
  induction T; intros; inversion H;
  try econstructor;
  try eapply IHT1; eauto; try eapply IHT2; eauto; try eapply IHT; eauto; subst;
  try inversion H0; eauto.

  - (* "TVarH" *) simpl. simpl in H0. unfold id in H0.
    assert (beq_nat x 0 = false) as E. apply beq_nat_false_iff. assumption.
    rewrite E.
    eapply cl_selh. lia.
Qed.

Lemma subst_open_commute_m: forall i j k k' j' V T2, closed (i+1) (j+1) k T2 -> closed 0 j' k' (TSel V) ->
    subst V (open_rec i (varH (j+1)) T2) = open_rec i (varH j) (subst V T2).
Proof.
  intros.
  generalize dependent i. generalize dependent j.
  induction T2; intros; inversion H; simpl; eauto; subst;
  try rewrite IHT2_1;
  try rewrite IHT2_2;
  try rewrite IHT2; eauto.
  - (* "TVarH" *) simpl. case_eq (beq_nat x 0); intros E.
    eapply closed_no_open. eapply closed_upgrade. eauto. lia.
    eauto.
  - (* "TVarB" *) simpl. case_eq (beq_nat i x); intros E.
    simpl. case_eq (beq_nat (j+1) 0); intros E2.
    eapply beq_nat_true_iff in E2. lia.
    subst. assert (j+1-1 = j) as A. lia. rewrite A. eauto.
    eauto.
Qed.

Lemma subst_open_commute: forall i j k k' V T2, closed (i+1) (j+1) k T2 -> closed 0 0 k' (TSel V) ->
    subst V (open_rec i (varH (j+1)) T2) = open_rec i (varH j) (subst V T2).
Proof.
  intros. eapply subst_open_commute_m; eauto.
Qed.

Lemma subst_open_zero: forall i i' k TX T2, closed i' 0 k T2 ->
    subst TX (open_rec i (varH 0) T2) = open_rec i TX T2.
Proof.
  intros. generalize dependent i'. generalize dependent i.
  induction T2; intros; inversion H; simpl; eauto;
  try solve [rewrite (IHT2_1 _ i'); eauto;
             rewrite (IHT2_2 _ (S i')); eauto;
             rewrite (IHT2_2 _ (S i')); eauto];
  try solve [rewrite (IHT2_1 _ i'); eauto;
             rewrite (IHT2_2 _ i'); eauto].
  subst.
  case_eq (beq_nat x 0); intros E. lia. lia.
  case_eq (beq_nat i x); intros E. eauto. eauto.
Qed.

Lemma Forall2_length: forall A B f (G1:list A) (G2:list B),
                        Forall2 f G1 G2 -> length G1 = length G2.
Proof.
  intros. induction H.
  eauto.
  simpl. eauto.
Qed.

Lemma nosubst_intro: forall i k T, closed i 0 k T -> nosubst T.
Proof.
  intros. generalize dependent i.
  induction T; intros; inversion H; simpl; eauto.
  lia.
Qed.

Lemma nosubst_open: forall i V T2, nosubst (TSel V) -> nosubst T2 -> nosubst (open_rec i V T2).
Proof.
  intros. generalize dependent i. induction T2; intros;
  try inversion H0; simpl; eauto; destruct v; eauto.
  case_eq (beq_nat i i0); intros E. eauto. eauto.
Qed.

(*
when and how we can replace with multiple environments:

stp2 G1 T1 G2 T2 (GH0 ++ [(vty GX TX)])

1) T1 closed

   stp2 G1 T1 G2' T2' (subst GH0)

2) G1 contains (GX TX) at some index x1

   index x1 G1 = (GX TX)
   stp2 G (subst (TVarF x1) T1) G2' T2'

3) G1 = GX

   stp2 G1 (subst TX T1) G2' T2'

4) G1 and GX unrelated

   stp2 ((GX,TX) :: G1) (subst (TVarF (length G1)) T1) G2' T2'

*)

(* ---- two-env substitution. first define what 'compatible' types mean. ---- *)

Definition compat (GX:venv) (TX: ty) (V: option vl) (G1:venv) (T1:ty) (T1':ty) :=
  (exists x1 v a c, indexr x1 G1 = Some (a,c,v) /\ V = Some v /\ GX = base v /\ val_type GX v TX /\ T1' = (subst (varF x1) T1)) \/
  (closed 0 0 (length G1) T1 /\ T1' = T1) \/ (* this one is for convenience: redundant with next *)
  (nosubst T1 /\ T1' = subst (varF 0) T1).


Definition compat2 (GX:venv) (TX: ty) (V: option vl) (p1:(bool*class*(venv*ty))) (p2:(bool*class*(venv*ty))) :=
  match p1, p2 with
      (a1,c1,(G1,T1)), (a2,c2,(G2,T2)) => (a1,c1,G1) = (a2,c2,G2) /\ compat GX TX V G1 T1 T2
  end.

Lemma closed_compat: forall GX TX V GXX TXX TXX' i j,
  compat GX TX V GXX TXX TXX' ->
  closed 0 j (length GXX) TX ->
  closed i (j+1) (length GXX) TXX ->
  closed i j (length GXX) TXX'.
Proof.
  intros. inversion H;[|destruct H2;[|destruct H2]].
  - destruct H2. destruct H2. destruct H2. destruct H2. destruct H2. destruct H3. destruct H4. destruct H4.
    destruct H5. rewrite H5.
    eapply closed_subst. eauto.
    eapply cl_sel. apply indexr_max in H2. lia.
  - destruct H2. rewrite H3.
    eapply closed_upgrade. eapply closed_upgrade_free. eauto. lia. lia.
  - subst. eapply closed_nosubst. eauto. eauto.
Qed.

Lemma indexr_compat_miss0: forall GH GH' GX TX V (GXX:venv) (TXX:ty) n a c ax cx,
      Forall2 (compat2 GX TX V) GH GH' ->
      indexr (n+1) (GH ++ [(a,c,(GX, TX))]) = Some (ax,cx,(GXX,TXX)) ->
      exists TXX', indexr n GH' = Some (ax,cx,(GXX,TXX')) /\ compat GX TX V GXX TXX TXX'.
Proof.
  intros. revert n H0. induction H.
  - intros. simpl. eauto. simpl in H0. assert (n+1 <> 0). lia.
    eapply beq_nat_false_iff in H. rewrite H in H0. inversion H0.
  - intros. simpl. destruct y.
    case_eq (beq_nat n (length l')); intros E.
    + simpl in H1. rewrite app_length in H1. simpl in H1.
      assert (n = length l'). eapply beq_nat_true_iff. eauto.
      assert (beq_nat (n+1) (length l + 1) = true). eapply beq_nat_true_iff.
      rewrite (Forall2_length _ _ _ _ _ H0). lia.
      rewrite H3 in H1. destruct x. inversion H1. subst. simpl in H.
      destruct p. destruct p0. destruct H. inversion H. subst. eexists. eauto.
    + simpl in H1. destruct x.
      assert (n <> length l'). eapply beq_nat_false_iff. eauto.
      assert (beq_nat (n+1) (length l + 1) = false). eapply beq_nat_false_iff.
      rewrite (Forall2_length _ _ _ _ _ H0). lia.
      rewrite app_length in H1. simpl in H1.
      rewrite H3 in H1.
      eapply IHForall2. eapply H1.
Qed.

Lemma compat_top: forall GX TX V G1 T1',
  compat GX TX V G1 TTop T1' -> closed 0 0 (length GX) TX -> T1' = TTop.
Proof.
  intros ? ? ? ? ? CC CLX. repeat destruct CC as [|CC]; ev; eauto.
Qed.

Lemma compat_bot: forall GX TX V G1 T1',
  compat GX TX V G1 TBot T1' -> closed 0 0 (length GX) TX -> T1' = TBot.
Proof.
  intros ? ? ? ? ? CC CLX. repeat destruct CC as [|CC]; ev; eauto.
Qed.

Lemma compat_mem: forall GX TX V G1 S1 U1 T1',
    compat GX TX V G1 (TMem S1 U1) T1' ->
    closed 0 0 (length GX) TX ->
    exists SA UA, T1' = TMem SA UA /\
                  compat GX TX V G1 S1 SA /\
                  compat GX TX V G1 U1 UA.
Proof.
  intros ? ? ? ? ? ? ? CC CLX.
  destruct CC as [|CC]; ev; subst.
  repeat eexists; eauto; solve [unfold compat; left; repeat eexists; eassumption].

  destruct CC as [|CC]; ev; subst;
  inversion H; subst;
  repeat eexists; eauto; solve [unfold compat; eauto].
Qed.

Lemma compat_mem_fwd2: forall GX TX V G1 T2 T2',
    compat GX TX V G1 T2 T2' ->
    compat GX TX V G1 (TMem TBot T2) (TMem TBot T2').
Proof.
  intros. repeat destruct H as [|H]; ev; repeat eexists; eauto.
  - left. repeat eexists; eauto. rewrite H3. eauto.
  - right. left. subst. eauto.
  - right. right. subst. simpl. eauto.
Qed.

Lemma compat_mem_fwd1: forall GX TX V G1 T1 T1',
    compat GX TX V G1 T1 T1' ->
    compat GX TX V G1 (TMem T1 TTop) (TMem T1' TTop).
Proof.
  intros. repeat destruct H as [|H]; ev; repeat eexists; eauto.
  - left. repeat eexists; eauto. rewrite H3. eauto.
  - right. left. subst. eauto.
  - right. right. subst. simpl. eauto.
Qed.

Lemma compat_sel: forall GX TX V G1 T1' (GXX:venv) (TXX:ty) x v a c,
    compat GX TX V G1 (TSel (varF x)) T1' ->
    closed 0 0 (length GX) TX ->
    closed 0 0 (length GXX) TXX ->
    indexr x G1 = Some (a,c,v) ->
    val_type GXX v TXX ->
    exists TXX', T1' = (TSel (varF x)) /\ compat GX TX V GXX TXX TXX'
.
Proof.
  intros ? ? ? ? ? ? ? ? ? ? ? CC CL CL1 IX HV.

  destruct CC.
  destruct H. destruct H. destruct H. destruct H. destruct H. destruct H0. destruct H1. destruct H2.
  simpl in H3. eexists. split. eauto. right. left. eauto.
  destruct H. destruct H. simpl in H0. eexists. split. eauto. right. left. eauto.
  destruct H. destruct H. simpl in H0. eexists. split. eauto. right. left. eauto.
Qed.

Lemma compat_selh: forall GX TX V G1 T1' GH0 GH0' (GXX:venv) (TXX:ty) a c ax cx x,
    compat GX TX V G1 (TSel (varH x)) T1' ->
    closed 0 0 (length GX) TX ->
    indexr x (GH0 ++ [(a,c,(GX, TX))]) = Some (ax,cx,(GXX, TXX)) ->
    Forall2 (compat2 GX TX V) GH0 GH0' ->
    (x = 0 /\ GXX = GX /\ TXX = TX) \/
    exists TXX',
      x > 0 /\ T1' = TSel (varH (x-1)) /\
      indexr (x-1) GH0' = Some (ax,cx,(GXX, TXX')) /\
      compat GX TX V GXX TXX TXX'
.
Proof.
  intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? CC CL IX FA.

  case_eq (beq_nat x 0); intros E.
  - left. assert (x = 0). eapply beq_nat_true_iff. eauto. subst x.
    rewrite indexr_hit0 in IX. inversion IX. eauto.
  - right. assert (x <> 0). eapply beq_nat_false_iff. eauto.
    assert (x > 0). unfold id. unfold id in H. lia.
    eapply (indexr_compat_miss0) in FA. destruct FA.
    destruct CC as [H2 | H2].

    destruct H2 as [x1 [x2 [x3 [x4 [H2 [H3 [H4 [H5]]]]]]]]. rename e into H6.
    simpl in H6.
    rewrite E in H6.
    eexists. split. lia. split; eauto.

    simpl in H2. destruct H2. destruct H2.
    inversion H2; subst. lia.

    destruct H2. rewrite E in H3.
    eexists. eauto.

    assert (x-1+1=x) as A. lia. rewrite A. eauto.
Qed.

Lemma compat_all: forall GX TX V G1 T1 T2 T1' n c1 c2,
    compat GX TX V G1 (TAll T1 c1 T2 c2) T1' ->
    closed 0 0 (length GX) TX -> closed 1 (n+1) (length G1) T2 ->
    exists TA TB, T1' = TAll TA c1 TB c2 /\
                  closed 1 n (length G1) TB /\
                  compat GX TX V G1 T1 TA /\
                  compat GX TX V G1 (open_rec 0 (varH (n+1)) T2) (open_rec 0 (varH n) TB).
Proof.
  intros ? ? ? ? ? ? ? ? ? ? CC CLX CL2. destruct CC.

  ev. simpl in H0. repeat eexists; eauto. eapply closed_subst; eauto using indexr_max.
  unfold compat. left. repeat eexists; eauto.
  unfold compat. left. repeat eexists; eauto. erewrite subst_open_commute; eauto.

  destruct H. destruct H. inversion H. repeat eexists. eauto. subst.
  eapply closed_upgrade_free. eauto. lia. unfold compat. eauto.
  unfold compat. eauto. right. right. subst.
  split. eapply nosubst_open. simpl. lia. eapply nosubst_intro. eauto. symmetry.
  assert (T2 = subst (varF 0) T2) as A. symmetry. eapply closed_no_subst. eauto.
  remember (open_rec 0 (varH n) T2) as XX. rewrite A in HeqXX. subst XX.
  eapply subst_open_commute. eauto. eauto.

  simpl in H. destruct H. destruct H. repeat eexists. eauto. eapply closed_nosubst. eauto. eauto.
  unfold compat. right. right. eauto.
  unfold compat. right. right. split. eapply nosubst_open. simpl. lia. eauto.
  erewrite subst_open_commute. eauto. eauto. eauto.
Qed.

Lemma compat_closed: forall GX TX V G T T' j,
  compat GX TX V G T T' ->
  closed 0 (j + 1) (length G) T ->
  closed 0 0 (length GX) TX ->
  closed 0 j (length G) T'.
Proof.
  intros. inversion H;[|destruct H2;[|destruct H2]].
  - destruct H2 as [x1 [v [a [c [Hindex [HeqV [HGX [Hv Heq]]]]]]]]. subst.
    apply closed_subst. eassumption.
    apply indexr_max in Hindex. apply cl_sel. lia.
  - destruct H2. subst.
    eapply closed_upgrade_free. eapply H2. lia.
  - subst.
    apply closed_nosubst. assumption. eauto.
Qed.

Lemma stp2_substitute_aux: forall n, forall G1 G2 T1 T2 GH m n1,
   stp2 false m G1 T1 G2 T2 GH n1 ->
   n1 <= n ->
   forall GH0 GH0' GX TX T1' T2' V a c,
     GX = base V ->
     GH = (GH0 ++ [(a,c,(GX, TX))]) ->
     val_type (base V) V TX ->
     closed 0 0 (length GX) TX ->
     compat GX TX (Some V) G1 T1 T1' ->
     compat GX TX (Some V) G2 T2 T2' ->
     Forall2 (compat2 GX TX (Some V)) GH0 GH0' ->
     stpd2 false m G1 T1' G2 T2' GH0'.
Proof.
  intros n. induction n.
  (* "z" *) intros. inversion H0. subst. inversion H; eauto.
  intros G1 G2 T1 T2 GH m n1 H NE. remember false as s.
  induction H; inversion Heqs.

   - (* "top" *)
    intros GH0 GH0' GXX TXX T1' T2' V ? ? ? ? ? CX IX1 IX2 FA.
    eapply compat_top in IX2.
    subst. eapply stpd2_top.
    eapply compat_closed. eassumption.
    rewrite app_length in H. simpl in H.
    erewrite <- Forall2_length. eapply H. eassumption.
    eassumption. assumption.

  - (* "bot" *)
    intros GH0 GH0' GXX TXX T1' T2' V ? ? ? ? ? CX IX1 IX2 FA.
    eapply compat_bot in IX1.
    subst. eapply stpd2_bot.
    eapply compat_closed. eassumption.
    rewrite app_length in H. simpl in H.
    erewrite <- Forall2_length. eapply H. eassumption.
    eassumption. assumption.

  - (* "mem" *)
    intros GH0 GH0' GXX TXX T1' T2' V ? ? ? ? ? CX IX1 IX2 FA.
    eapply compat_mem in IX1. repeat destruct IX1 as [? IX1].
    eapply compat_mem in IX2. repeat destruct IX2 as [? IX2].
    subst. eapply stpd2_mem.
    eapply IHn; eauto; try lia.
    eapply IHn; eauto; try lia.
    eauto. eauto.

  - (* "sel1" *)
    intros GH0 GH0' GXX TXX T1' T2' V ? ? ? ? ? CX IX1 IX2 FA.

    assert (length GH = length GH0 + 1). subst GH. eapply app_length.
    assert (length GH0 = length GH0') as EL. eapply Forall2_length. eauto.

    eapply (compat_sel GXX TXX (Some V) G1 T1' (base v) TX) in IX1. repeat destruct IX1 as [? IX1].

    assert (compat GXX TXX (Some V) (base v) TX TX) as CPX. right. left. eauto.

    subst.
    eapply stpd2_sel1. eauto. eauto. eauto.
    eapply IHn; eauto; try lia.
    eapply compat_mem_fwd2. eauto.
    eauto. eauto. eauto. eauto.

  - (* "sel2" *)
    intros GH0 GH0' GXX TXX T1' T2' V ? ? ? ? ? CX IX1 IX2 FA.

    assert (length GH = length GH0 + 1). subst GH. eapply app_length.
    assert (length GH0 = length GH0') as EL. eapply Forall2_length. eauto.

    eapply (compat_sel GXX TXX (Some V) G2 T2' (base v) TX) in IX2. repeat destruct IX2 as [? IX2].

    assert (compat GXX TXX (Some V) (base v) TX TX) as CPX. right. left. eauto.

    subst.
    eapply stpd2_sel2. eauto. eauto. eauto.
    eapply IHn; eauto; try lia.
    eapply compat_mem_fwd1. eauto.
    eauto. eauto. eauto. eauto.

  - (* "selx" *)
    intros GH0 GH0' GXX TXX T1' T2' V ? ? ? ? ? CX IX1 IX2 FA.

    assert (length GH = length GH0 + 1). subst GH. eapply app_length.
    assert (length GH0 = length GH0') as EL. eapply Forall2_length. eauto.

    assert (T1' = TSel (varF x1)). {
      destruct IX1. ev. eauto.
      destruct H6. ev. auto.
      destruct H6. ev. eauto.
    }
    assert (T2' = TSel (varF x2)). {
      destruct IX2. ev. eauto.
      destruct H7. ev. auto.
      destruct H7. ev. eauto.
    }
    subst.
    eapply stpd2_selx. eauto. eauto.

  - (* "sela1" *)
    intros GH0 GH0' GXX TXX T1' T2' V ? ? ? ? ? CX IX1 IX2 FA.

    assert (length GH = length GH0 + 1). subst GH. eapply app_length.
    assert (length GH0 = length GH0') as EL. eapply Forall2_length. eauto.

    assert (compat GXX TXX (Some V) G1 (TSel (varH x)) T1') as IXX. eauto.

    eapply (compat_selh GXX TXX (Some V) G1 T1' GH0 GH0' GX TX) in IX1. repeat destruct IX1 as [? IX1].

    destruct IX1.
    + (* "x = 0" *)
      repeat destruct IXX as [|IXX]; ev.
      * subst. simpl. inversion H10; subst.
        eapply stpd2_sel1. eauto. eauto. eauto.
        eapply IHn; eauto; try lia. right. left. auto.
        eapply compat_mem_fwd2. eauto.
      * subst. inversion H7. subst. lia.
      * subst. destruct H9. eauto.
    + (* "x > 0" *)
      ev. subst.
      eapply stpd2_sela1. eauto.
      assert (x-1+1=x) as A by lia.
      remember (x-1) as x1. rewrite <- A in H0.
      eapply compat_closed. eauto. eauto. eauto.
      eapply IHn; eauto; try lia.
      eapply compat_mem_fwd2. eauto.
    (* remaining obligations *)
    + eauto. + subst GH. eauto. + eauto.

  - (* "sela2" *)
    intros GH0 GH0' GXX TXX T1' T2' V ? ? ? ? ? CX IX1 IX2 FA.

    assert (length GH = length GH0 + 1). subst GH. eapply app_length.
    assert (length GH0 = length GH0') as EL. eapply Forall2_length. eauto.

    assert (compat GXX TXX (Some V) G2 (TSel (varH x)) T2') as IXX. eauto.

    eapply (compat_selh GXX TXX (Some V) G2 T2' GH0 GH0' GX TX) in IX2. repeat destruct IX2 as [? IX2].

    destruct IX2.
    + (* "x = 0" *)
      repeat destruct IXX as [|IXX]; ev.
      * subst. simpl. inversion H10; subst.
        eapply stpd2_sel2. eauto. eauto. eauto.
        eapply IHn; eauto; try lia. right. left. auto.
        eapply compat_mem_fwd1. eauto.
      * subst. inversion H7. subst. lia.
      * subst. destruct H9. eauto.
    + (* "x > 0" *)
      ev. subst.
      eapply stpd2_sela2. eauto.
      assert (x-1+1=x) as A by lia.
      remember (x-1) as x1. rewrite <- A in H0.
      eapply compat_closed. eauto. eauto. eauto.
      eapply IHn; eauto; try lia.
      eapply compat_mem_fwd1. eauto.
    (* remaining obligations *)
    + eauto. + subst GH. eauto. + eauto.

  - (* "selax" *)

    intros GH0 GH0' GXX TXX T1' T2' V ? ? ? ? ? CX IX1 IX2 FA.

    assert (length GH = length GH0 + 1). subst GH. eapply app_length.
    assert (length GH0 = length GH0') as EL. eapply Forall2_length. eauto.

    assert (compat GXX TXX (Some V) G1 (TSel (varH x)) T1') as IXX1. eauto.
    assert (compat GXX TXX (Some V) G2 (TSel (varH x)) T2') as IXX2. eauto.

    destruct v as [[aa cc ][GX TX]].
    eapply (compat_selh GXX TXX (Some V) G1 T1' GH0 GH0' GX TX a c aa cc) in IX1. repeat destruct IX1 as [? IX1].
    eapply (compat_selh GXX TXX (Some V) G2 T2' GH0 GH0' GX TX a c aa cc) in IX2. repeat destruct IX2 as [? IX2].

    assert (not (nosubst (TSel (varH 0)))). unfold not. intros. simpl in H1. eauto.
    assert (not (closed 0 0 (length G1) (TSel (varH 0)))). unfold not. intros. inversion H6. lia.
    assert (not (closed 0 0 (length G2) (TSel (varH 0)))). unfold not. intros. inversion H7. lia.

    destruct x; destruct IX1; ev; try lia; destruct IX2; ev; try lia; subst.
    + (* "x = 0" *)
      repeat destruct IXX1 as [IXX1|IXX1]; ev; try contradiction.
      repeat destruct IXX2 as [IXX2|IXX2]; ev; try contradiction.
      * (* "sel-sel" *)
        subst. simpl. inversion H16; subst. inversion H2; subst.
        eapply stpd2_selx. eauto. eauto.
    + (* "x > 0" *)
      destruct IXX1; destruct IXX2; ev; subst; eapply stpd2_selax; eauto.
    (* leftovers *)
    + eauto. + subst. eauto. + eauto. + eauto. + subst. eauto. + eauto.

  - (* "all" *)
    intros GH0 GH0' GX TX T1' T2' V ? ? ? ? ? CX IX1 IX2 FA.

    assert (length GH = length GH0 + 1). subst GH. eapply app_length.
    assert (length GH0 = length GH0') as EL. eapply Forall2_length. eauto.

    eapply compat_all in IX1. repeat destruct IX1 as [? IX1].
    eapply compat_all in IX2. repeat destruct IX2 as [? IX2].

    subst.

    eapply stpd2_all. eauto.
    + eapply IHn; eauto; try lia.
    + eauto.
    + eauto.
    + eauto.
    + subst.
      eapply IHn. eauto. lia. simpl. eauto.
      change ((true,c,(G2, T3)) :: GH0 ++ [(a,c0,(base V, TX))]) with (((true,c,(G2, T3)) :: GH0) ++ [(a,c0,(base V, TX))]).
      reflexivity.
      eauto. eauto.
      rewrite app_length. simpl. rewrite EL. eauto.
      rewrite app_length. simpl. rewrite EL. eauto.
      eapply Forall2_cons. simpl. eauto. eauto.
    + eauto.
    + eauto. subst GH. rewrite <-EL. eapply closed_upgrade_free. eauto. lia.
    + eauto.
    + eauto. subst GH. rewrite <-EL. eapply closed_upgrade_free. eauto. lia.
  - (* "wrapf" *)
    intros. subst. eapply stpd2_wrapf. eapply IHn; eauto; try lia.
  - (* "transf" *)
    intros. subst. 
    apply stp2_extend2 with (v1:=(true,First,V)) in H.
    apply stp2_extend1 with (v1:=(true,First,V)) in H0.
    eapply stpd2_transf.

    eapply IHn; eauto; try lia. 
    unfold compat. simpl. left.
    exists (length G2). exists V. exists true. exists First.
    rewrite <- beq_nat_refl. split; eauto.

    eapply IHn; eauto; try lia.
    unfold compat. simpl. left.
    exists (length G2). exists V. exists true. exists First.
    rewrite <- beq_nat_refl. split; eauto.
Qed.

Lemma stp2_substitute: forall G1 G2 T1 T2 GH m,
   stpd2 false m G1 T1 G2 T2 GH ->
   forall GH0 GH0' GX TX T1' T2' V a c,
     GX = base V ->
     GH = (GH0 ++ [(a,c,(GX, TX))]) ->
     val_type (base V) V TX ->
     closed 0 0 (length GX) TX ->
     compat GX TX (Some V) G1 T1 T1' ->
     compat GX TX (Some V) G2 T2 T2' ->
     Forall2 (compat2 GX TX (Some V)) GH0 GH0' ->
     stpd2 false m G1 T1' G2 T2' GH0'.
Proof.
  intros. repeat eu. eapply stp2_substitute_aux; eauto.
Qed.

(* ### Relating Static and Dynamic Subtyping ### *)
Lemma inv_vtp_half: forall G v T GH,
  val_type G v T ->
  exists T0, val_type (base v) v T0 /\ closed 0 0 (length (base v)) T0 /\
             stpd2 false false (base v) T0 G T GH.
Proof.
  intros. inversion H; subst.
  - eexists. split; try split.
    + simpl. econstructor. eassumption. ev. eapply stp2_reg1 in s. apply s.
    + ev. eapply stp2_closed1 in H1. simpl in H1. apply H1.
    + eapply stpd2_downgrade. ev. eexists. simpl.
      eapply stp2_extendH_mult0. eassumption.
  - eexists. split; try split.
    + simpl. econstructor; try eassumption. reflexivity. ev. eapply stp2_reg1 in s. apply s.
    + ev. eapply stp2_closed1 in H2. simpl in H2. apply H2.
    + eapply stpd2_downgrade. ev. eexists. simpl.
      eapply stp2_extendH_mult0. eassumption.
Qed.

Lemma exists_GYL: forall GX GY GU GL,
  wf_envh GX GY (GU ++ GL) ->
  exists GYU GYL, GY = GYU ++ GYL /\ wf_envh GX GYL GL.
Proof.
  intros. remember (GU ++ GL) as G. generalize dependent HeqG. generalize dependent GU. generalize dependent GL. induction H; intros.
  - exists (@nil (bool * class * (venv * ty))). exists (@nil (bool * class * (venv * ty))). simpl. split. reflexivity. symmetry in HeqG. apply app_eq_nil in HeqG.
    inversion HeqG. subst. eauto.
  - induction GU.
    + rewrite app_nil_l in HeqG.
      exists (@nil (bool * class * (venv * ty))). eexists. rewrite app_nil_l. split. reflexivity.
      rewrite <- HeqG. eauto.
    + simpl in HeqG. inversion HeqG.
      specialize (IHwf_envh GL GU H2). destruct IHwf_envh as [GYU [GYL [IHA IHB]]].
      exists ((a,c,(vvs, t))::GYU). exists GYL. split. rewrite IHA. simpl. reflexivity.
      apply IHB.
Qed.

Lemma stp_to_stp2: forall G1 GH T1 T2,
  stp G1 GH T1 T2 ->
  forall GX GY, wf_env GX G1 -> wf_envh GX GY GH ->
  stpd2 false false GX T1 GX T2 GY.
Proof.
  intros G1 G2 T1 T2 ST. induction ST; intros GX GY WX WY; eapply stpd2_wrapf.
  - (* "top" *)
    eapply stpd2_top. erewrite wfh_length; eauto. erewrite wf_length; eauto.
  - (* "bot" *)
    eapply stpd2_bot. erewrite wfh_length; eauto. erewrite wf_length; eauto.
  - (* "mem" *) eapply stpd2_mem; eauto.
  - (* "sel1" *)
    assert (exists v, indexr x GX = Some (a,c,v) /\ val_type GX v TX) as A.
    eapply indexr_safe_ex. eauto. eauto.
    destruct A as [? [? VT]].
    eapply inv_vtp_half in VT. ev.
    eapply stpd2_sel1. eauto. eauto. eauto. eapply stpd2_trans. eauto. eauto.
  - (* "sel2" *)
    assert (exists v : vl, indexr x GX = Some (a,c,v) /\ val_type GX v TX) as A.
    eapply indexr_safe_ex. eauto. eauto.
    destruct A as [? [? VT]].
    eapply inv_vtp_half in VT. ev.
    eapply stpd2_sel2. eauto. eauto. eauto. eapply stpd2_trans. eauto. eauto.
  - (* "selx" *) eauto.
    assert (exists v0 : vl, indexr x GX = Some (a,c,v0) /\ val_type GX v0 v) as A.
    eapply indexr_safe_ex. eauto. eauto. eauto.
    destruct A as [? [? ?]].
    eapply stpd2_selx; eauto.
  - (* "sela1" *)
    assert (exists v, indexr x GY = Some (a,c,v) /\ valh_type GX GY v TX) as A.
    eapply index_safeh_ex. eauto. eauto. eauto.
    destruct A as [? [? VT]]. destruct x0.
    inversion VT. subst.
    eapply stpd2_sela1. eauto. erewrite wf_length; eauto. eauto.
  - (* "sela2" *)
    assert (exists v, indexr x GY = Some (a,c,v) /\ valh_type GX GY v TX) as A.
    eapply index_safeh_ex. eauto. eauto. eauto.
    destruct A as [? [? VT]]. destruct x0.
    inversion VT. subst.
    eapply stpd2_sela2. eauto. erewrite wf_length; eauto. eauto.
  - (* "selax" *)
    assert (exists v0, indexr x GY = Some (a,c,v0) /\ valh_type GX GY v0 v) as A.
    eapply index_safeh_ex. eauto. eauto. eauto.
    destruct A as [? [? VT]]. destruct x0.
    destruct VT. subst.
    eapply stpd2_selax. eauto.
  - (* "all" *)
    subst x.
    assert (length GY = length GH) as A. eapply wfh_length; eauto.
    assert (length GX = length G1) as B. eapply wf_length; eauto.
    eapply stpd2_all. eauto. eauto. eauto. eauto.
    rewrite A. rewrite B. eauto.
    rewrite A. rewrite B. eauto.
    rewrite A.
    eapply IHST2. eauto. eapply wfeh_cons. eauto.
Qed.

(* ### Inversion Lemmas ### *)

Lemma invert_app: forall venv vf vx T1 T2 c c2,
  val_type venv vf (TAll T1 c T2 c2) ->
  val_type venv vx T1 ->
  closed 0 0 (length venv) T2 ->
  exists env tenv x y T3 T4 c4,
    vf = (vabs env T3 c y c4) /\
    length env = x /\
    wf_env env tenv /\
    has_type ((true,c,T3)::tenv) y c4 (open (varF x) T4) /\
    stpd2 true true venv T1 env T3 [] /\
    stpd2 true true ((true,c,vx)::env) (open (varF x) T4) venv T2 [] /\
    subcl c4 c2.
Proof.
  intros. inversion H; ev; tryfalse_invert.
  inversion H5. subst.
  eexists. eexists. eexists. eexists. eexists. eexists. eexists. eexists.
  reflexivity.
  repeat split; eauto. remember (length venv1) as x.

  eapply stpd2_upgrade; eauto.
  eapply stpd2_upgrade.
  eapply inv_vtp_half with (GH:=nil) in H0. ev.
  simpl in H26.
  assert (stpd2 false false venv1 (open (varH 0) T3) venv0 (open (varH 0) T2) [(true,c,(base vx, x))]) as A. {
    eapply stpd2_narrow. eassumption. eexists. eassumption.
  }
  assert (open (varH 0) T2=T2) as EH2. {
    rewrite <- closed_no_open with (i:=0) (j:=0) (k:=(length venv0)); eauto.
  }
  assert (open (varF (length venv1)) T2=T2) as EF2. {
    rewrite <- closed_no_open with (i:=0) (j:=0) (k:=(length venv0)); eauto.
  }
  rewrite EH2 in A.
  apply stp2_substitute with (GH0:=nil) (V:=vx) (GX:=base vx) (T1:=(open (varH 0) T3)) (T2:=T2) (TX:=x) (GH:=[(true,c,(base vx, x))]) (a:=true) (c:=c); eauto.
  apply stpd2_extend1. eapply A.
  left. exists (length venv1). exists vx. exists true. exists c.
  split. simpl. rewrite <- beq_nat_refl. reflexivity.
  split. reflexivity. split. reflexivity. split. assumption.
  unfold open. erewrite subst_open_zero. reflexivity.
  simpl in H25. eapply H25.
  right. left. eauto.
Qed.




Lemma sanitize_commute: forall {X} venv0 a c c1 (v:X),
  (sanitize_env c ((a,c1,v)::venv0)) =
  match c with
    | First =>
      match (a,c1,v) with
          | (true, First, x) => (true, First, x)
          | (true, Second, x) => (false, Second, x)
          | (false, c, x) => (false, c, x)
      end
    | Second => (a,c1,v)
  end ::(sanitize_env c venv0).
Proof.
  intros X G. induction G; intros. 
  destruct c; destruct a; destruct c1; compute; eauto.
  destruct c; destruct a; destruct c1; compute; eauto.
Qed.


Lemma index_unsanitize: forall venv0 xarg (vx:vl) c c1,
  indexr xarg (sanitize_env c venv0) = Some (true, c1, vx) ->                      
  indexr xarg venv0 = Some (true, c1, vx).
Proof.
  intros G. induction G; intros.
  destruct c; compute in H; inversion H.
  destruct a as [[? ?] ?].
  rewrite sanitize_commute in H. simpl in H.
  assert (length (sanitize_env c G) = length G).
  unfold sanitize_env. destruct c; try rewrite map_length; eauto.
  case_eq (beq_nat xarg (length (sanitize_env c G))); intros E.
  - rewrite E in H. simpl. rewrite H0 in E. rewrite E.
    destruct c; destruct b; destruct c0; inversion H; eauto.
  - rewrite E in H. simpl. rewrite H0 in E. rewrite E.
    eauto. 
Qed.

Lemma index_sanitize: forall {X} (venv0:env X) xarg a (c:class) c1 (v:X),
  indexr xarg venv0 = Some (a, c1, v) ->
  exists b c0, indexr xarg (sanitize_env c venv0) = Some (b, c0, v).
Proof.
  intros X G. induction G; intros.
  destruct c; compute in H; inversion H.
  destruct a as [[? ?] ?].
  rewrite sanitize_commute.
  assert (length (sanitize_env c G) = length G).
  unfold sanitize_env. destruct c; try rewrite map_length; eauto.
  case_eq (beq_nat xarg (length G)); intros E.
  - simpl in H. rewrite E in H. inversion H. subst.
    simpl. rewrite H0. rewrite E. 
    destruct c; destruct a0; destruct c1; inversion H; eauto. 
  - simpl in H. rewrite E in H. simpl. rewrite H0. rewrite E.
    eauto. 
Qed.



Lemma invert_dapp: forall venv vf vx xarg T1 T2 c c1 c2,
  val_type venv vf (TAll T1 c1 T2 c2) ->
  val_type venv vx T1 ->
  indexr xarg (sanitize_env c1 venv) = Some (true,c,vx) ->
  closed 0 0 (length venv) (open (varF xarg) T2) ->
  exists env tenv x y T3 T4 c4,
    vf = (vabs env T3 c1 y c4) /\
    length env = x /\
    wf_env env tenv /\
    has_type ((true,c1,T3)::tenv) y c4 (open (varF x) T4) /\
    stpd2 true true venv T1 env T3 [] /\
    stpd2 true true ((true,c1,vx)::env) (open (varF x) T4) venv (open (varF xarg) T2) [] /\
    subcl c4 c2.
Proof.
  intros. inversion H; ev; tryfalse_invert.
  inversion H6. subst.
  eexists. eexists. eexists. eexists. eexists. eexists. eexists. eexists. reflexivity.
  repeat split; eauto; remember (length venv1) as x.

  eapply stpd2_upgrade; eauto.
  eapply stpd2_upgrade.
  eapply inv_vtp_half with (GH:=nil) in H0. ev.
  simpl in H27.
  assert (stpd2 false false venv1 (open (varH 0) T3) venv0 (open (varH 0) T2) [(true,c1,(base vx, x0))]) as A. {
    eapply stpd2_narrow. eassumption. eexists. eassumption.
  }
  apply stp2_substitute with (GH0:=nil) (V:=vx) (GX:=base vx) (T1:=(open (varH 0) T3)) (T2:=(open (varH 0) T2)) (TX:=x0) (GH:=[(true,c1,(base vx, x0))]) (a:=true) (c:=c1); eauto.
  apply stpd2_extend1. eapply A.
  left. exists (length venv1). exists vx. exists true. exists c1.
  split. simpl. rewrite <- beq_nat_refl. reflexivity.
  split. reflexivity. split. reflexivity. split. assumption.
  subst x. unfold open. erewrite subst_open_zero. reflexivity.
  simpl in H26. eapply H26.
  left. exists xarg. exists vx. exists true. exists c.
  split. eapply index_unsanitize. eapply H1. 
  split. reflexivity. split. reflexivity. split. assumption.
  unfold open. erewrite subst_open_zero. reflexivity.
  simpl in H27. eapply H27.
Qed.



(* Note: the following two lemmas are admitted without 
   formal proof. 

   The formal proofs would be a bit tedious, and it is
   clear that the lemmas must hold:

   The stp2 judgement is set up in such a way that
   all lookups ignore the boolean visibility flag
   and the 1st/2nd class specifier.

   More precisely, lookups in stp2 have only one of three 
   forms, and in each case a and c are not otherwise bound:

      indexr x G2 = Some (a, c, vty GX TX)  (* concrete env, precise type *)

      indexr x G1 = Some (a, c,v)           (* concrete env, imprecise type *)

      indexr x GH = Some (a, c, (GX, TX))   (* abstract env *)

   Thus, changing a or c cannot change the behavior
   of stp2. So adding or removing a call to sanitize_env
   (which can only change a to false) cannot have any 
   effect on stp2.

   Proving this formally in Coq would take the same 
   structure as stp2_extend and stp2_splice. 
*)

Lemma stp2_unsanitize2: forall G1 G2 H T1 T2 a b c n,
  stp2 a b G1 T1 (sanitize_env c G2) T2 H n ->
  stp2 a b G1 T1 G2 T2 H n.
Proof. admit. Admitted.

Lemma stp2_sanitize: forall G1 G2 H T1 T2 a b c n,
  stp2 a b G1 T1 G2 T2 H n ->
  stp2 a b (sanitize_env c G1) T1 G2 T2 H n /\
  stp2 a b G1 T1 (sanitize_env c G2) T2 H n.
Proof. admit. Admitted.

Lemma val_type_unsanitize : forall env res T n,
  val_type (sanitize_env n env) res T ->
  val_type env res T.
Proof.
  intros. inversion H.
  - subst. econstructor. eauto.
    destruct H1. eapply stp2_unsanitize2 in H1. eauto.
  - subst. econstructor. eauto. eauto. eauto.
    destruct H3. eapply stp2_unsanitize2 in H2. eauto.
Qed.

Lemma val_type_sanitize : forall env res T n,
  val_type env res T ->
  val_type (sanitize_env n env) res T.
Proof.
  intros. inversion H.
  - subst. econstructor. eauto.
    destruct H1. eapply stp2_sanitize in H1. ev. eauto.
  - subst. econstructor. eauto. eauto. eauto.
    destruct H3. eapply stp2_sanitize in H2. ev. eauto.
Qed.

Lemma wf_san: forall venv0 env0 c,
  wf_env venv0 env0 ->
  wf_env (sanitize_env c venv0) (sanitize_env c env0).
Proof.
  intros. induction H. compute. destruct c; eauto.
  rewrite sanitize_commute. rewrite sanitize_commute. 
  destruct c; destruct a; destruct c0; eapply wfe_cons; eauto.
  eapply (val_type_sanitize _ _ _ First) in H. simpl in H. eapply H.
  eapply (val_type_sanitize _ _ _ First) in H. simpl in H. eapply H.
  eapply (val_type_sanitize _ _ _ First) in H. simpl in H. eapply H.
  eapply (val_type_sanitize _ _ _ First) in H. simpl in H. eapply H.
Qed.

(* ### Type Safety ### *)
(* If term type-checks and the term evaluates without timing-out,
   the result is not stuck, but a value.
 *)

Lemma indexr_san : forall {X} (venv0 : env X) c c1 c2 i v,
    subcl c1 c2 ->
    indexr i (sanitize_env c1 venv0) = Some (true, c, v) ->
    indexr i (sanitize_env c2 venv0) = Some (true, c, v).
Proof.
  intros X venv0. induction venv0; intros.
  - destruct c1; destruct c2; eauto.
  - destruct a; destruct p; rewrite sanitize_commute; rewrite sanitize_commute in H0.
    destruct c1; destruct c2; eauto.
    + case_eq (beq_nat i (length (sanitize_env First venv0))); intros.
      symmetry in H1.
      eapply beq_nat_eq in H1. subst i.
      eapply indexr_hit in H0; eauto. destruct b; destruct c0; inversion H0; subst.
      eapply indexr_hit2.
      unfold sanitize_env. try rewrite map_length; eauto.
      reflexivity.
      unfold indexr.
      assert ((length (sanitize_env Second venv0)) = length (sanitize_env First venv0)).
      unfold sanitize_env. try rewrite map_length; eauto.
      rewrite H2. rewrite H1. eapply IHvenv0. eassumption.
      eapply indexr_miss in H0. eassumption.
      eapply beq_nat_false in H1. eassumption.
    + inversion H.
Qed.

Theorem full_safety : forall n e c tenv venv res T,
  teval n venv e c = Some res -> has_type tenv e c T -> wf_env venv tenv ->
  res_type venv res T.

Proof.
  intros n. induction n.
  (* 0 *)   intros. inversion H.
  (* S n *) intros. destruct e; inversion H.

  - (* "Var" *) subst res.
    remember (tvar i) as e. clear H. remember (sanitize_env c venv0) as sanvenv.
      generalize dependent sanvenv. induction H0; inversion Heqe; intros; subst.
    + destruct (indexr_safe_ex (sanitize_env c venv0) (sanitize_env c env0) T1 i true c1) as [v [I V]]; eauto. eapply wf_san; eauto. 
      rewrite I. eapply not_stuck. eapply val_type_unsanitize. eapply V.

    + intuition. eapply restp_widen. specialize (H4 (sanitize_env c venv0)).
      intuition.
      -- remember (indexr i (sanitize_env c venv0)) as idxr. destruct idxr.
        --- destruct p; destruct p; destruct b. eassumption. inversion H3.
        --- inversion H3.
      -- eapply stpd2_upgrade. eapply stp_to_stp2; eauto.

  - (* "Typ" *)
    remember (ttyp t) as e. induction H0; inversion Heqe; subst.
    + eapply not_stuck. eapply v_ty; eauto.
      eapply stp2_refl. simpl. erewrite wf_length; eauto.
    + eapply restp_widen. eapply IHhas_type; eauto.
      eapply stpd2_upgrade. eapply stp_to_stp2; eauto.

  - (* "Abs" *) subst res.
    remember (tabs t c0 e c1) as xe.
    induction H0; inversion Heqxe; intros; subst.
    + econstructor. eapply v_abs; eauto. eapply wf_san; eauto.
      destruct c; simpl; try rewrite map_length; eauto.
      assert (stpd2 true true venv0 (TAll t c0 T2 c1) venv0 (TAll t c0 T2 c1) []). eapply stp2_refl. simpl. erewrite wf_length; eauto.
      eu. eexists. eapply stp2_sanitize. eauto.
    + intuition. eapply restp_widen. eassumption.
      eapply stpd2_upgrade. eapply stp_to_stp2; eauto.

  - (* "App" *)
    dependent induction H0.
    +
      remember (teval n venv0 e1 Second) as tf.

      destruct tf as [rf|]; tryfalse_invert.
      assert (res_type venv0 rf (TAll T1 c1 T2 c2)) as HRF. (* "HRF" *) subst. eapply IHn; eauto.
      inversion HRF as [? vf].

      subst rf. remember vf as rvf. destruct vf; try (subst rvf; false_invert).
      assert (c1 = c).
        destruct c; destruct c1;
        try (subst rvf ; false_invert); eauto.
        subst rvf. inversion H2; subst. destruct H16. inversion H4.
        subst rvf. inversion H2; subst. destruct H16. inversion H4.
      assert (subcl c0 c2).
        destruct c0; destruct c2;
        try (subst rv ; false_invert); eauto.
        subst rvf. inversion H2. subst. destruct H17. inversion H4; subst. inversion H16.

      subst rvf.
      remember (teval n venv0 e2 c) as tx.

      destruct tx as [rx|]; tryfalse_invert.
      assert (res_type venv0 rx T1) as HRX. (* "HRX" *) subst. eapply IHn. symmetry. eassumption.
      eassumption. eassumption.
      inversion HRX as [? vx].

      subst. remember (vabs e t c t0 c0) as vf.
      
      destruct (invert_app venv0 vf vx T1 T2 c c2) as
          [env1 [tenv [x0 [y0 [T3 [T4 [c4 [EF [FRX [WF [HTY [STX [STY]]]]]]]]]]]]].
      eauto. eauto. erewrite wf_length; eauto.
      (* now we know it's a closure, and we have has_type evidence *)

      subst vf. inversion EF. subst.
      
      assert (res_type ((true,c,vx)::env1) res (open (varF (length env1)) T4)) as HRY.
        (* "HRY" *)
          subst. eapply IHn. eauto. eauto.
          (* wf_env x *) econstructor. eapply valtp_widen; eauto.
                         eapply stpd2_extend2. eauto. eauto.

      inversion HRY as [? vy].

      eapply not_stuck. eapply valtp_widen; eauto.

      (* f = vty case *)
      subst rvf. inversion H2. subst. ev. inversion H4. 
    +
      remember (teval n venv0 e1 Second) as tf.

      destruct tf as [rf|]; tryfalse_invert.
      assert (res_type venv0 rf (TAll T1 cf T2 cr)) as HRF. (* "HRF" *) subst. eapply IHn; eauto.
      inversion HRF as [? vf].

      subst rf. remember vf as rvf. destruct vf; try (subst rvf; tryfalse_invert).
      assert (cf = c).
        destruct cf; destruct c;
        try (subst rvf; false_invert); eauto.
        inversion H2. subst. destruct H16. inversion H4.
        inversion H2. subst. destruct H16. inversion H4.
      assert (subcl c0 cr).
        destruct cr; destruct c0;
        try (subst rvf; false_invert); eauto.
        inversion H2. subst. destruct H17. inversion H4. subst. inversion H16.

      remember (teval n venv0 (tvar x) c) as tx.

      destruct tx as [rx|]; tryfalse_invert.
      assert (res_type venv0 rx T1) as HRX. (* "HRX" *) subst. eapply IHn; eauto.
      inversion HRX as [? vx].

      subst. remember (vabs e t c t0 c0) as vf.
      destruct n. inversion H3. inversion Heqtx. simpl in Heqtx. 
      remember (indexr x (sanitize_env c venv0)) as ix.
      destruct ix as [[[[|] ] ] |]; tryfalse_invert.
      inversion H5. subst v.
      
      destruct (invert_dapp venv0 vf vx x T1 T2 c1 c cr) as
          [env1 [tenv [x0 [y0 [T3 [T4 [c4 [EF [FRX [WF [HTY [STX [STY HCL]]]]]]]]]]]]].
      subst. inversion H2; subst. destruct H17. econstructor.
      eassumption. eassumption. reflexivity. exists x0.
      exact H4.
      eassumption. symmetry in Heqix. eassumption.
      erewrite wf_length; eauto.
      (* now we know it's a closure, and we have has_type evidence *)

      subst vf. inversion EF. subst e. 
      
      assert (res_type ((true,c,vx)::env1) res (open (varF x0) T4)) as HRY.
        (* "HRY" *)
          subst. eapply IHn. eauto. eauto. 
          (* wf_env x *) econstructor. eapply valtp_widen; eauto.
          eapply stpd2_extend2. eauto.
          (* wf_env   *) eauto.
      inversion HRY as [? vy].

      eapply not_stuck. eapply valtp_widen; eauto.

      (* contradictions *)
      inversion H2. subst. ev. inversion H4.

    + eapply restp_widen. eapply IHhas_type; eauto.
      eapply stpd2_upgrade. eapply stp_to_stp2; eauto.
Qed.