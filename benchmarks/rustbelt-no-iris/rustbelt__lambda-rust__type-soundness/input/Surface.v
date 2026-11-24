Require Export Inclusion.

(* Appendix §1.3: CPS, let-normal programs. Erasure uses the existing
   λRust expressions, not a new operational semantics. *)
Inductive instruction :=
| ITrue | IFalse | INum (n : Z)
| IFun (self : string) (args : list string) (ret : string) (code : body)
| IPath (p : path)
| IAdd (p q : path) | ISub (p q : path) | ILe (p q : path)
| INew (words : nat) | IDelete (words : nat) (p : path)
| IRead (p : path) | IWrite (dst src : path)
| ISumUnit (tag : nat) (dst : path)
| ISumWrite (tag : nat) (dst src : path)
| ICopy (words : nat) (dst src : path)
| ISumCopy (tag words : nat) (dst src : path)
with body :=
| FLet (result : string) (instr : instruction) (next : body)
| FLetCont (name : string) (args : list string) (code next : body)
| FNewLft (next : body)
| FEndLft (next : body)
| FIf (p : path) (yes no : body)
| FCase (p : path) (branches : list body)
| FJump (cont : string) (args : list string)
| FCall (func : string) (args : list path) (cont : string).

Fixpoint erase_path (p : path) : expr :=
  match p with
  | PVar x => Var x
  | POffset p0 n => BinOp OffsetOp (erase_path p0) (Lit (LitInt (Z.of_nat n)))
  end.

Definition let_expr (x : binder) (e next : expr) : expr :=
  App (Rec BAnon [x] next) [e].
Definition seq_expr (e next : expr) : expr := let_expr BAnon e next.
Definition poison := Lit LitPoison.
Definition int_expr (z : Z) := Lit (LitInt z).
Definition test_expr (test yes no : expr) := Case test [no; yes].
Definition skip_expr := seq_expr poison poison.
Definition offset_expr (p : expr) (n : Z) := BinOp OffsetOp p (int_expr n).
Definition read_expr := Read Na1Ord.
Definition write_expr := Write Na1Ord.

(* The executable definitions from the artifact's lang/lib/new_delete.v
   and lang/lib/memcpy.v, written without the original notation or Iris. *)
Local Open Scope string_scope.
Definition new_expr : expr :=
  Rec BAnon [BNamed "n"]
    (test_expr (BinOp LeOp (Var "n") (int_expr 0))
      (Lit (LitLoc (42%positive, 1337))) (Alloc (Var "n"))).
Definition delete_expr : expr :=
  Rec BAnon [BNamed "n"; BNamed "loc"]
    (test_expr (BinOp LeOp (Var "n") (int_expr 0))
      poison (Free (Var "n") (Var "loc"))).
Definition memcpy_expr : expr :=
  Rec (BNamed "memcpy") [BNamed "dst"; BNamed "len"; BNamed "src"]
    (test_expr (BinOp LeOp (Var "len") (int_expr 0)) poison
      (seq_expr (write_expr (Var "dst") (read_expr (Var "src")))
        (App (Var "memcpy")
          [offset_expr (Var "dst") 1; BinOp MinusOp (Var "len") (int_expr 1);
           offset_expr (Var "src") 1]))).

Definition memcpy (n : nat) (p q : expr) := App memcpy_expr [p; int_expr (Z.of_nat n); q].

Definition write_tag (tag : nat) (p : expr) := write_expr (offset_expr p 0) (int_expr (Z.of_nat tag)).

Fixpoint erase_body (f : body) : expr :=
  match f with
  | FLet x i next => let_expr (BNamed x) (erase_instruction i) (erase_body next)
  | FLetCont k xs code next =>
      let_expr (BNamed k) (Rec (BNamed k) (map BNamed xs) (erase_body code)) (erase_body next)
  | FNewLft next => seq_expr poison (erase_body next)
  | FEndLft next => seq_expr skip_expr (erase_body next)
  | FIf p yes no => test_expr (erase_path p) (erase_body yes) (erase_body no)
  | FCase p branches => Case (read_expr (erase_path p)) (map erase_body branches)
  | FJump k xs => App (Var k) (map Var xs)
  | FCall f ps k =>
      (* The artifact's call macro ends the call lifetime on return.
         Pick a binder different from k before expanding the macro. *)
      let r := String.append k "'" in
      let ret := Rec BAnon [BNamed r] (seq_expr skip_expr (App (Var k) [Var r])) in
      App (Var f) (ret :: map erase_path ps)
  end
with erase_instruction (i : instruction) : expr :=
  match i with
  | ITrue => int_expr 1
  | IFalse => int_expr 0
  | INum n => int_expr n
  | IFun f xs k code => Rec (BNamed f) (map BNamed (k :: xs)) (erase_body code)
  | IPath p => erase_path p
  | IAdd p q => BinOp PlusOp (erase_path p) (erase_path q)
  | ISub p q => BinOp MinusOp (erase_path p) (erase_path q)
  | ILe p q => BinOp LeOp (erase_path p) (erase_path q)
  | INew n => App new_expr [int_expr (Z.of_nat n)]
  | IDelete n p => App delete_expr [int_expr (Z.of_nat n); erase_path p]
  | IRead p => read_expr (erase_path p)
  | IWrite p q => write_expr (erase_path p) (erase_path q)
  | ISumUnit tag p => write_tag tag (erase_path p)
  | ISumWrite tag p q =>
      seq_expr (write_tag tag (erase_path p))
        (write_expr (offset_expr (erase_path p) 1) (erase_path q))
  | ICopy n p q => memcpy n (erase_path p) (erase_path q)
  | ISumCopy tag n p q =>
      seq_expr (write_tag tag (erase_path p))
        (memcpy n (offset_expr (erase_path p) 1) (erase_path q))
  end.
