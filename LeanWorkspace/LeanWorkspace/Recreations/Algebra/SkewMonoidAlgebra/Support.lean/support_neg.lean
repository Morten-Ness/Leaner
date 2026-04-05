import Mathlib

open scoped Pointwise

variable {k G : Type*}

variable [AddCommGroup k]

theorem support_neg (p : SkewMonoidAlgebra k G) : (-p).support = p.support := by
  rw [support, toFinsupp_neg, Finsupp.support_neg, support_toFinsupp]

