Require Import Metalib.Metatheory.

Definition i := nat.

Inductive co : Set :=
 | co_id : co
 | co_trans (c1:co) (c2:co)
 | co_top : co
 | co_arr (c1:co) (c2:co)
 | co_pair (c1:co) (c2:co)
 | co_proj1 : co
 | co_proj2 : co
 | co_distArr : co
 | co_distRcd (l:i)
 | co_rcd (l:i) (c:co)
 | co_topArr : co
 | co_topRcd (l:i).

Inductive styp : Set :=
 | styp_top : styp
 | styp_nat : styp
 | styp_and (A:styp) (B:styp)
 | styp_arrow (A:styp) (B:styp)
 | styp_rcd (l:i) (A:styp)  .

Inductive st : Set :=
 | st_ty (A:styp)
 | st_la (l:i).

Definition ls : Set := list st.

Fixpoint calAnd (fs : ls) : co :=
  match fs with
  | nil => co_id
  | cons l fs' =>
    match l with
    | st_ty _ => (co_trans (co_arr co_id (calAnd fs')) co_distArr)
    | st_la l => (co_trans (co_rcd l (calAnd fs')) (co_distRcd l))
    end
  end.

Fixpoint calTop (fs : ls) : co :=
  match fs with
  | nil => co_top
  | cons l fs' =>
    match l with
    | st_ty _ =>  (co_trans (co_arr co_id (calTop fs')) (co_trans (co_arr co_top co_top) (co_trans co_topArr co_top)))
    | st_la l => (co_trans (co_rcd l (calTop fs')) (co_topRcd l))
    end
  end.

Inductive sub : styp -> styp -> co -> Prop :=
 | S_refl : forall (A:styp),
     sub A A co_id
 | S_trans : forall (A1 A3:styp) (c1 c2:co) (A2:styp),
     sub A2 A3 c1 ->
     sub A1 A2 c2 ->
     sub A1 A3 (co_trans c1 c2)
 | S_top : forall (A:styp),
     sub A styp_top co_top
 | S_topArr :
     sub styp_top (styp_arrow styp_top styp_top) co_topArr
 | S_topRcd : forall (l:i),
     sub styp_top (styp_rcd l styp_top) (co_topRcd l)
 | S_arr : forall (A1 A2 B1 B2:styp) (c1 c2:co),
     sub B1 A1 c1 ->
     sub A2 B2 c2 ->
     sub (styp_arrow A1 A2) (styp_arrow B1 B2) (co_arr c1 c2)
 | S_and : forall (A1 A2 A3:styp) (c1 c2:co),
     sub A1 A2 c1 ->
     sub A1 A3 c2 ->
     sub A1 (styp_and A2 A3) (co_pair c1 c2)
 | S_andl : forall (A1 A2:styp),
     sub (styp_and A1 A2) A1 co_proj1
 | S_andr : forall (A1 A2:styp),
     sub (styp_and A1 A2) A2 co_proj2
 | S_distArr : forall (A1 A2 A3:styp),
     sub (styp_and  (styp_arrow A1 A2)   (styp_arrow A1 A3) ) (styp_arrow A1 (styp_and A2 A3)) co_distArr
 | S_rcd : forall (l:i) (A B:styp) (c:co),
     sub A B c ->
     sub (styp_rcd l A) (styp_rcd l B) (co_rcd l c)
 | S_distRcd : forall (l:i) (A B:styp),
     sub (styp_and (styp_rcd l A) (styp_rcd l B)) (styp_rcd l (styp_and A B)) (co_distRcd l).

Inductive ASub : ls -> styp -> styp -> co -> Prop :=
 | A_nat :
     ASub  nil  styp_nat styp_nat co_id
 | A_rcdNat : forall (l:i) (fs:ls) (A:styp) (c:co),
     ASub fs A styp_nat c ->
     ASub  (cons (st_la  l )  fs )  (styp_rcd l A) styp_nat (co_rcd l c)
 | A_rcd : forall (fs:ls) (A:styp) (l:i) (B:styp) (c:co),
     ASub  ( fs  ++ (cons (st_la  l ) nil))  A B c ->
     ASub fs A (styp_rcd l B) c
 | A_top : forall (fs:ls) (A:styp),
     ASub fs A styp_top (co_trans  (calTop  fs )  co_top)
 | A_and : forall (fs:ls) (A B1 B2:styp) (c1 c2:co),
     ASub fs A B1 c1 ->
     ASub fs A B2 c2 ->
     ASub fs A (styp_and B1 B2) (co_trans  (calAnd  fs )  (co_pair c1 c2))
 | A_arr : forall (fs:ls) (A B1 B2:styp) (c:co),
     ASub  ( fs  ++ (cons (st_ty  B1 ) nil))  A B2 c ->
     ASub fs A (styp_arrow B1 B2) c
 | A_andN1 : forall (fs:ls) (A1 A2:styp) (c:co),
     ASub fs A1 styp_nat c ->
     ASub fs (styp_and A1 A2) styp_nat (co_trans c co_proj1)
 | A_andN2 : forall (fs:ls) (A1 A2:styp) (c:co),
     ASub fs A2 styp_nat c ->
     ASub fs (styp_and A1 A2) styp_nat (co_trans c co_proj2)
 | A_arrNat : forall (A:styp) (fs:ls) (A1 A2:styp) (c1 c2:co),
     ASub  nil  A A1 c1 ->
     ASub fs A2 styp_nat c2 ->
     ASub  (cons (st_ty  A )  fs )  (styp_arrow A1 A2) styp_nat (co_arr c1 c2).
