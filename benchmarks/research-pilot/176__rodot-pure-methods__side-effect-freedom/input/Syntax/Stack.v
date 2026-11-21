Set Implicit Arguments.

Require Import LibExtra Vars Terms Heap Env SyntaxClasses TransformCollect Bool.

Inductive frame : Set :=
  | frame_let : trm -> frame.

Inductive stack: Set :=
  | stack_nil: stack
  | stack_cons (f: frame) (fs: stack): stack
.

Fixpoint stack_length (fs : stack) : nat :=
  match fs with
  | stack_nil => 0
  | stack_cons _ fs' => (stack_length fs') + 1
  end.

Definition frame_fv fr := match fr with frame_let c => fv c end.

Instance FrameFreeVar : FreeVar frame := frame_fv.

Fixpoint stack_fv s: vars :=
  match s with
  | stack_nil => \{}
  | stack_cons f fs => (fv f) \u (@fv stack stack_fv fs)
  end.

Instance StackFreeVar : FreeVar stack := stack_fv.

Definition frame_subst_var x y fr :=
  match fr with frame_let c => frame_let (subst_var x y c) end.

Instance FrameSubstVar: SubstVar frame := frame_subst_var.

Fixpoint stack_subst_var x y st :=
  match st with
    | stack_nil => stack_nil
    | stack_cons f fs => stack_cons (subst_var x y f) (@subst_var stack stack_subst_var x y fs)
  end.

Instance StackSubstVar: SubstVar stack := stack_subst_var.

Definition frame_open n x fr :=
  match fr with frame_let c => frame_let (open_rec n x c) end.

Instance FrameOpenable: Openable frame := frame_open.

Fixpoint stack_open n x st :=
  match st with
    | stack_nil => stack_nil
    | stack_cons f fs => stack_cons (open_rec (S n) x f) (@open_rec stack stack_open n x fs)
  end.

Instance StackOpenable:  Openable stack := stack_open.

Instance FrameAbstractSyntax :
  AbstractSyntax FrameOpenable FrameFreeVar FrameSubstVar := {}.

Instance StackAbstractSyntax :
  AbstractSyntax StackOpenable StackFreeVar StackSubstVar := {}.

Definition collect_frame {C: Type} (df : C) (f : avar -> C) (comb: C -> C -> C) (fr: frame) : C :=
  match fr with
  | frame_let t => (collect df f comb t)
  end.

Instance FrameCollect : Collect AvarAbstractSyntax FrameAbstractSyntax :=
  @collect_frame.

Fixpoint collect_stack {C: Type} (df : C) (f : avar -> C) (comb: C -> C -> C) (st: stack) : C :=
  match st with
  | stack_nil => df
  | (stack_cons fr fs) => comb (collect df f comb fr) (@collect _ _ _ _ AvarAbstractSyntax _ _ _ _ StackAbstractSyntax (@collect_stack) C df f comb fs)
  end.

Instance StackCollect : Collect AvarAbstractSyntax StackAbstractSyntax :=
  @collect_stack.

Definition transform_frame (f : avar -> nat -> avar) (fr : frame) (n : nat) : frame :=
  match fr with
  | frame_let t => frame_let (transform f t n)
  end.

Instance FrameTransform : Transform AvarAbstractSyntax FrameAbstractSyntax :=
  @transform_frame.

Fixpoint transform_stack (f : avar -> nat -> avar) (st : stack) (n : nat) : stack :=
  match st with
  | stack_nil => stack_nil
  | (stack_cons fr fs) => (stack_cons (transform f fr (S n)) (@transform _ _ _ _ AvarAbstractSyntax _ _ _ _ StackAbstractSyntax transform_stack f fs n))
  end.

Instance StackTransform : Transform AvarAbstractSyntax StackAbstractSyntax :=
  @transform_stack.

Fixpoint stack_append (fs1 fs2: stack) :=
  match fs1 with
  | stack_nil => fs2
  | stack_cons f fs => stack_cons f (stack_append fs fs2)
  end.

Definition stack_suffix fs1 fs2 := exists fs3, fs2 = stack_append fs3 fs1.
