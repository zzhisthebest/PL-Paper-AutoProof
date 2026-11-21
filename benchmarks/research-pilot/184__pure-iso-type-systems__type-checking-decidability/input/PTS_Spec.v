Inductive sort : Set := srt_level (n:nat).

Record PTSSpec : Type :=
  {pts_axiom : sort -> sort -> Prop;
   pts_rules : sort -> sort -> sort -> Prop;
   pts_axuniq : forall s1 s2 s3,
                pts_axiom s1 s2 -> pts_axiom s1 s3 -> s2 = s3;
   pts_reluniq : forall s1 s2 s3 s3',
                 pts_rules s1 s2 s3 -> pts_rules s1 s2 s3' -> s3 = s3';
   pts_axdec: forall s1, (exists s2, pts_axiom s1 s2) \/
                         ~(exists s2, pts_axiom s1 s2);
   pts_reldec: forall s1 s2, (exists s3, pts_rules s1 s2 s3) \/
                             ~(exists s3, pts_rules s1 s2 s3)
  }.

Parameter PTS : PTSSpec.
