Require Import FSets.

Module Make (X : UsualOrderedType).

Module E := X.

Module F := FSetList.Make E.

Module OFacts := OrderedType.OrderedTypeFacts E.

End Make.
