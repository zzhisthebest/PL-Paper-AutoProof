From oadt Require Import base.

Instance bool_join : Join bool := orb.

Instance bool_top : Top bool := true.

Instance bool_bot : Bottom bool := false.

Instance bool_le : SqSubsetEq bool := implb.
