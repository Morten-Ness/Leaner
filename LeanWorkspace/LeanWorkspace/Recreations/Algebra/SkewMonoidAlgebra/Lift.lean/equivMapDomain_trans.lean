import Mathlib

variable {k G H : Type*}

variable [AddCommMonoid k]

theorem equivMapDomain_trans {G' G'' : Type*} (f : G ≃ G') (g : G' ≃ G'')
    (l : SkewMonoidAlgebra k G) :
    SkewMonoidAlgebra.equivMapDomain (f.trans g) l = SkewMonoidAlgebra.equivMapDomain g (SkewMonoidAlgebra.equivMapDomain f l) := by
  ext x; rfl

