Set Implicit Arguments.

Require Import LibExtra DotTactics AbstractSyntax.

Require Import Context Equivalence Indep GeneralTyping.

Require Import Transformation TransformationTerm TransformationLifting Weakening EWeakening Substitution.

Require Import TypingHelpers Narrowing.

Require Import ReadableSyntax.

Require Import Visibility.

Require Import Lia.

Require Import Sealing.

Require Import Subenvironments.

Require Import Closedness.

Require Import TransformCollect.

Section WithTypingMode.

Context (typing_mode: Mode).

Inductive trf_swap_calls_local: TermTransform :=
  trf_swap_calls_local_at (x1 x2: var) (m1 m2: met_label) (xp1 xp2 y1 y2: var) t G e (T1 T2 T TZ1 TZ2: typ):
    ctx_ok G ->
    ok e ->
    closed t ->
    fresh (ctx_dom G \u ctx_fv G \u fv_renv e \u fv T \u fv T1 \u fv T2) 2 (y1::y2::nil)%list ->

    G ⁏ e ⊢ x1 ∶ ❪❴ᵐ m1 ∶ 𝖭 , TZ1 → ⊤ ❵❫ ->
    G ⁏ e ⊢ x2 ∶ ❪❴ᵐ m2 ∶ 𝖭 , TZ2 → ⊤ ❵❫ ->
    G ⁏ e ⊢ ❪𝖭❫ <: TZ1 ->
    G ⁏ e ⊢ ❪𝖭❫ <: TZ2 ->
    G ⁏ e ⊢ ❪Call $x1․m1 $xp1❫ ∶ T1 ->
    G ⁏ e ⊢ ❪Call $x2․m2 $xp2❫ ∶ T2 ->
    G ⁏ e ⊢ xp1 ∶ TZ1 ->
    G ⁏ e ⊢ xp2 ∶ TZ2 ->
    G §ˣ y2 ~ T2 §ˣ y1 ~ T1 ⁏ e ⊢ t ∶ T ->
    〈G ⁏ e ⊢ ❪Let y1=Call $x1․m1 $xp1 In Let y2=Call $x2․m2 $xp2 In t❫ ∶ T〉 ∼trf_swap_calls_local∼> 〈G ⁏ e ⊢ ❪Let y2=Call $x2․m2 $xp2 In Let y1=Call $x1․m1 $xp1 In t❫ ∶ T〉.

End WithTypingMode.
