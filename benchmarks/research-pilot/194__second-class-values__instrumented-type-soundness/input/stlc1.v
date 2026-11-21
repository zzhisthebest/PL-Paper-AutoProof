Require Export Arith.EqNat.

Require Export Arith.

Require Export List.

Require Export Lia.

Export ListNotations.

Definition id := nat.

Inductive class : Type :=
  | First  : class
  | Second : class
.

Definition subcl (n m : class) :=
  match n, m with
  | First, Second => true
  | Second, First => false
  | _, _ => true
  end.

Inductive ty : Type :=
  | TBool  : ty
  | TFun   : ty -> class -> ty -> class -> ty
.

Inductive var : Type :=
  | V : class -> id -> var
.

Inductive tm : Type :=
  | ttrue  : tm
  | tfalse : tm
  | tvar   : var -> tm
  | tapp   : tm -> tm -> tm
  | tabs   : class -> tm -> class -> tm
.

Inductive env {X: Type} :=
  | Def (fc : list X) (sc : list X) (sc_min : nat).

Inductive vl : Type :=
  | vbool : bool -> vl
  | vabs  : @env vl -> class -> tm -> class -> vl
.

Definition venv := @env vl.

Definition tenv := @env ty.

Fixpoint index {X : Type} (n : id) (l : list X) : option X :=
  match l with
    | [] => None
    | a :: l'  => if Nat.eqb n (length l') then Some a else index n l'
  end.

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

End env_tests.

Definition sanitize_any {X : Type} (l : @env X) (n:nat): @env X :=
  match l with
    | Def l1 l2 _ => Def l1 l2 n
  end.

Definition sanitize_env {X : Type} (c : class) (l : @env X) : @env X :=
  match c,l  with
    | First, Def _ l2 _ => sanitize_any l (length l2)
    | Second, _ => l
  end.

Definition expand_env {X : Type} (l : @env X) (x : X) (c : class) : (@env X) :=
match l with
| Def l1 l2 m =>
   match c with
   | First => @Def X (x::l1) l2 m
   | Second => @Def X l1 (x::l2) m
   end
end
.

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

Let app_id_true := (tapp identity_ff ttrue).

End has_type_tests.

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

End teval_tests.

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
