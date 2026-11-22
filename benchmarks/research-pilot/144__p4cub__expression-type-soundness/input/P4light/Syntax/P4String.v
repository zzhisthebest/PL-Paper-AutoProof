Require Import Coq.Strings.String.

Require Import Coq.Classes.EquivDec.

Require Import Coq.Bool.Bool.

Require Import Coq.Lists.List.

Require Poulet4.Utils.AList Poulet4.Utils.AListUtil.

Import ListNotations.

Record t (tags_t: Type) :=
  { tags: tags_t;
    str: string }.

Arguments tags {tags_t}.

Arguments str {tags_t}.

Definition empty_str [tags_t: Type] (tag : tags_t) :  (t tags_t) :=
  {| tags := tag; str := "" |}.

Definition strip [tags_t: Type] (s: t tags_t) :=
  {| tags := tt; str := s.(str) |}.

Definition equiv [tags_t: Type] (s1 s2: t tags_t) : Prop :=
  s1.(str) = s2.(str).

Definition equivb [tags_t: Type] (s1 s2: t tags_t) :=
  String.eqb s1.(str) s2.(str).

Definition nequivb [tags_t: Type] (s1 s2: t tags_t) :=
  negb (String.eqb s1.(str) s2.(str)).

Definition eq_const [tags_t: Type] (s1: t tags_t) (s2: string) :=
  String.eqb s1.(str) s2.

#[global] Instance EquivEquivalence (tags_t : Type) : Equivalence (@equiv tags_t) :=
  ltac:(constructor;
    [ constructor
    | intros [] [] H; unfold equiv in *; simpl in *; subst; auto
    | intros [] [] [] H1 H2; unfold equiv in *; simpl in *; subst; auto ]).

#[global] Instance P4StringEqDec (tags_t : Type) : EqDec (t tags_t) (@equiv tags_t) :=
  ltac:(intros [t1 s1] [t2 s2];
    unfold Equivalence.equiv; unfold complement; simpl; unfold equiv; simpl;
    apply String.string_dec).

Section AList.

Variables tags_t V : Type.

Definition AList := AList.AList (t tags_t) V (@equiv tags_t).

Definition clear_AList_tags : AList -> AList.StringAList V :=
    List.map (fun '(x, v) => (str x,v)).

End AList.

Arguments clear_AList_tags {_} {_}.
