Set Implicit Arguments.

Require Import Coq.Bool.Bool.

Require Import LibExtra.

Require Import SyntaxClasses SyntaxClassProperties SyntaxClassDepth ListSyntaxClasses SyntaxClassLemmas.

Generalizable Variables A B.

Class Collect `(AS : AbstractSyntax B) `(AS': AbstractSyntax A) :=
  collect : forall {C : Type}, C -> (B -> C) -> (C -> C -> C) -> A -> C.

Arguments collect _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ !_ /.

Class ListLikeCollect `{ASB : AbstractSyntax B} `{ASA: AbstractSyntax A}
      {C: Set} `{ASC: AbstractSyntax C} {TL: ToList C A}
      (CBC: Collect ASB ASC) (CBA: Collect ASB ASA) :=
  collect_fold_right_map : forall (C' : Type) (df : C') f comb (a : A),
    collect df f comb a =
    List.fold_right comb df (List.map (collect df f comb) (to_list a)).

Class CollectCompose `(C: Collect B A) :=
  collect_compose :
    forall {C D} (f : C -> D) g comb1 comb2 i,
      (forall x y, f (comb1 x y) = comb2 (f x) (f y)) ->
      f ∘ (collect i g comb1) = collect (f i) (f ∘ g) comb2.

Class CollectReflect `(C: Collect B A) :=
  collect_reflect : forall P p,
    (forall b, (P b) <-> (p b) = true) ->
    forall {bl} a,
      ((collect (Is_true bl) P or a) <-> (collect bl p orb a) = true).

Class FvCollect `(Collect) :=
  fv_collect : fv = collect (\{}) fv (@union var).

Section AboutCollectCompose.

Context `{C: Collect B A}.

Context {CC: CollectCompose C}.

End AboutCollectCompose.

Class Transform `(AS : AbstractSyntax B) `(AS': AbstractSyntax A) :=
  transform : (B -> nat -> B) -> A -> nat -> A.

Arguments transform _ _ _ _ _ _ _ _ _ _ _ _ !_ /.

Class ListLikeTransform `{ASB : AbstractSyntax B} `{ASA: AbstractSyntax A}
      {C: Set} `{ASC: AbstractSyntax C}
      {TL: ToList C A} {FL: OfList C A} {LL: ListLike TL FL}
      (TBC: Transform ASB ASC) (TBA: Transform ASB ASA) :=
  transform_map_f : forall f n a,
    transform f a n = map_f (fun c => transform f c n) a.

Class TransformId `(T: Transform B A) :=
  transform_id : forall x n,
    transform (ignore_second id) x n = x.

Class TransformCompose `(T: Transform B A) :=
  transform_compose : forall f g,
    (transform f) ∘∘ (transform g) = transform (f ∘∘ g).

Class TransformShift `(AS : AbstractSyntax B) `(AS': AbstractSyntax A) (T: Transform AS AS') :=
  transform_shift f X n m: transform f X (n + m) = transform (fun X' n' => f X' (n' + m)) X n.

Class OpenTransform `(Transform) :=
  open_transform : forall n x,
    (open_depth_rec n x) = transform (open_depth_rec n x).

Class SubstTransform `(Transform) :=
  subst_transform : forall x y,
    (ignore_second (subst_var x y)) = transform (ignore_second (subst_var x y)).

Class SealTransform `(Transform B A)  `(Sealable B)  `(Sealable A) :=
  seal_transform : forall n x,
    (seal_depth_rec n x) = transform (seal_depth_rec n x).

Class CollectTransform
      `{ASB : AbstractSyntax B} `{ASA : AbstractSyntax A}
      (C : Collect ASB ASA) (T : Transform ASB ASA) :=
  collect_transform: forall bl p a f g,
    (collect bl p andb a) = true ->
    transform (dec_apply p f g) a = transform f a.

Section AboutTransformSyntax.

Context `{OA: Openable A} {FA: FreeVar A} {SA: SubstVar A}.

Context `{OB: Openable B} {FB: FreeVar B} {SB: SubstVar B}.

Context {ASB: AbstractSyntax OB FB SB} {ASA: AbstractSyntax OA FA SA}.

Context {C: Collect ASB ASA} {CC: CollectCompose C} {CR: CollectReflect C}
          {FC: FvCollect C}.

Context {T: Transform ASB ASA} {TI: TransformId T} {TC: TransformCompose T}
          {OT: OpenTransform T} {ST: SubstTransform T}.

Context {CT: CollectTransform C T}.

Section OpenCompose.

Context {OTA: OpenTwice OB}.

Context {OTC: OpenCommut OB}.

End OpenCompose.

Section SubstOpenCommut.

Context {SF: SubstOpenCommut ASB}.

End SubstOpenCommut.

Section SubstCommut.

Context {OTC: SubstCommut ASB}.

End SubstCommut.

Section ListLike.

Context {SC: Set}.

Context `{ASSC: AbstractSyntax SC}.

Context {CSC: Collect ASB ASSC}.

Context {CCSC: CollectCompose CSC} {CRSC: CollectReflect CSC}
            {FCSC: FvCollect CSC}.

Context {TSC: Transform ASB ASSC}.

Context {TISC: TransformId TSC} {TCSC: TransformCompose TSC}
            {OTSC: OpenTransform TSC} {STSC: SubstTransform TSC}.

Context {TCSSC: CollectTransform CSC TSC}.

Context {TL: ToList SC A} {FL: OfList SC A} {LL: ListLike TL FL}.

Section ListLikeCollect.

Context {LLC: ListLikeCollect CSC C}.

End ListLikeCollect.

Section ListLikeTransform.

Context {LLT: ListLikeTransform TSC T}.

End ListLikeTransform.

End ListLike.

Section DecideFvClosing.

Context {DFv: DecideFv ASB}.

Context {DFvS: ReflectFv DFv}.

Instance CollectDecideFv : DecideFv ASA :=
      (fun x => collect false (fun a => dec_fv x a) orb).

Section SubstFresh.

Context {SI: SubstitutionInner DFvS}.

Context {SF: SubstFresh ASB}.

End SubstFresh.

Section Closing.

Context {Cl: Closing ASB}.

Context {OC: OpenClose Cl} {CO: CloseOpen Cl} {SOC: SubstOpenClose Cl} {CS: CloseSubst Cl} {CCo: CloseCommut Cl} {SCCo: SubstCloseCommut Cl} {OCCo: OpenCloseCommut Cl}.

Instance TransformClosing : Closing ASA :=
        (fun n x a => transform (close_depth_rec n x) a 0).

Section CloseUnbound.

Context {CU: CloseUnbound Cl}.

Context {CI: ClosingInner DFvS Cl}.

End CloseUnbound.

Section TransformCloseDepth.

Context {TS : TransformShift T}.

End TransformCloseDepth.

End Closing.

End DecideFvClosing.

Section SealOpen.

Context {XA: Sealable A} {XB: Sealable B}.

Context {OTA: SealOpen ASB XB} {OTSC: SealTransform T XB XA}.

End SealOpen.

Section SealClose.

Context {XA: Sealable A} {XB: Sealable B}.

Context {CB: Closing ASB}.

Context {OTA: SealClose ASB XB CB} {OTSC: SealTransform T XB XA}.

End SealClose.

End AboutTransformSyntax.
