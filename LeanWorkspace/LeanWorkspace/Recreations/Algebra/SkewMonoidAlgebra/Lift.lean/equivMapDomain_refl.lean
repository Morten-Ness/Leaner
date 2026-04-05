import Mathlib

variable {k G H : Type*}

variable [AddCommMonoid k]

theorem equivMapDomain_refl (l : SkewMonoidAlgebra k G) : SkewMonoidAlgebra.equivMapDomain (Equiv.refl _) l = l := by
  ext x; rfl

