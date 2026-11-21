Require Import Utf8.

Require Import Binding.Lib Binding.Set Binding.Auto.

Require Import Lang.FOmegaEq.Kinds Lang.FOmegaEq.Types.

Import DED_kind.

Inductive ax := L | R.

Inductive value {V : Set} :=
| v_var (x : V) : value
| v_unit : value
| v_lam (e : @expr (inc V)) : value
| v_pair (v₁ v₂ : value) : value
| v_inj (a : ax) (v : value) : value
| v_tlam (e : expr) : value
| v_pack (v : value) : value
| v_roll (v : value) : value
| v_lamC  (e : expr) : value
| v_withC (v : value) : value
| v_fix (e : @expr (inc (inc V))) : value
with expr {V : Set} :=
| e_val (v : value) : expr
| e_bind (e₁ : expr) (e₂ : @expr (inc V)) : expr
| e_app (v₁ v₂ : value) : expr
| e_tapp (v : value) : expr
| e_proj (a : ax) (v : value) : expr
| e_abort (v : value) : expr
| e_case (v : value) (e₁ e₂ : @expr (inc V)) : expr
| e_unpack (v : value) (e : @expr (inc V)) : expr
| e_unroll (v : value) : expr
| e_cabort : expr
| e_capp (v : value) : expr
| e_lwith (v : value) (e : @expr (inc V)) : expr.

Arguments value V%bind : clear implicits.

Arguments expr  V%bind : clear implicits.

Declare Scope syn_scope.

Delimit Scope syn_scope with syn.

Coercion e_val : value >-> expr.

Coercion e_app : value >-> Funclass.

Notation "e₁ >>= e₂" := (e_bind e₁ e₂) (at level 45, right associativity) : syn_scope.

Notation "'ƛ' e" := (v_lam e) (at level 60) : syn_scope.

Notation "⟨⟩" := v_unit : syn_scope.

Notation "⟨ v ⟩ᶜ" := (v_withC v) : syn_scope.

Notation "⟨ v₁ , v₂ ⟩" := (v_pair v₁ v₂) : syn_scope.

Notation "'Λ' e" := (v_tlam e) (at level 60) : syn_scope.

Notation "'ƛᶜ' e" := (v_lamC e) (at level 60) : syn_scope.

Notation "'rec' e" := (v_fix e) (at level 60) : syn_scope.

Local Open Scope bind_scope.

Local Open Scope syn_scope.

Fixpoint emap {A B : Set} (f : A [→] B) (e : expr A) : expr B :=
  match e with
  | e_val v => vmap f v
  | e₁ >>= e₂ => emap f e₁ >>= emap (f ↑) e₂
  | e_app v₁ v₂ => (vmap f v₁) (vmap f v₂)
  | e_tapp v => e_tapp (vmap f v)
  | e_proj x v => e_proj x (vmap f v)
  | e_abort v => e_abort (vmap f v)
  | e_case v e₁ e₂ => e_case (vmap f v) (emap (f ↑) e₁) (emap (f ↑) e₂)
  | e_unpack v e => e_unpack (vmap f v) (emap (f ↑) e)
  | e_unroll v => e_unroll (vmap f v)
  | e_cabort => e_cabort
  | e_capp v => e_capp (vmap f v)
  | e_lwith v e => e_lwith (vmap f v) (emap (f ↑) e)
  end
with vmap {A B : Set} (f : A [→] B) (v : value A) : value B :=
       match v with
       | v_var x => v_var (f x)
       | ƛ e => ƛ (emap (f ↑) e)
       | Λ e => Λ (emap f e)
       | ⟨⟩ => ⟨⟩
       | ⟨v₁, v₂⟩ => ⟨vmap f v₁, vmap f v₂⟩
       | v_inj x v => v_inj x (vmap f v)
       | v_pack v => v_pack (vmap f v)
       | v_roll v => v_roll (vmap f v)
       | ƛᶜ e => v_lamC (emap f e)
       | ⟨v⟩ᶜ => ⟨vmap f v⟩ᶜ
       | rec e => rec (emap ((f ↑) ↑) e)
       end.

#[export] Instance FMap_expr : FunctorCore expr := @emap.

#[export] Instance FMap_val  : FunctorCore value := @vmap.

#[export] Instance SPC_val : SetPureCore value := @v_var.

Fixpoint ebind {X Y : Set} (f : X [⇒] Y) (e : expr X) : expr Y :=
  match e with
  | e_val v => vbind f v
  | e₁ >>= e₂ => ebind f e₁ >>= ebind (f ↑) e₂
  | e_app v₁ v₂ => (vbind f v₁) (vbind f v₂)
  | e_tapp v => e_tapp (vbind f v)
  | e_proj x v => e_proj x (vbind f v)
  | e_abort v => e_abort (vbind f v)
  | e_case v e₁ e₂ => e_case (vbind f v) (ebind (f ↑) e₁) (ebind (f ↑) e₂)
  | e_unpack v e => e_unpack (vbind f v) (ebind (f ↑) e)
  | e_unroll v => e_unroll (vbind f v)
  | e_cabort => e_cabort
  | e_capp v => e_capp (vbind f v)
  | e_lwith v e => e_lwith (vbind f v) (ebind (f ↑) e)
  end
with vbind {X Y : Set} (f : X [⇒] Y) (v : value X) : value Y :=
       match v with
       | v_var x => f x
       | ƛ e => ƛ (ebind (f ↑) e)
       | Λ e => Λ (ebind f e)
       | ⟨⟩ => ⟨⟩
       | ⟨v₁, v₂⟩ => ⟨vbind f v₁, vbind f v₂⟩
       | v_inj x v => v_inj x (vbind f v)
       | v_pack v => v_pack (vbind f v)
       | v_roll v => v_roll (vbind f v)
       | ƛᶜ  e => ƛᶜ (ebind f e)
       | ⟨v⟩ᶜ => ⟨vbind f v⟩ᶜ
       | rec e => rec (ebind ((f ↑) ↑) e)
       end.

#[export] Instance BindCore_expr : BindCore expr := @ebind.

#[export] Instance BindCore_val  : BindCore value := @vbind.
