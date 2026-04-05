import Mathlib

open scoped Pointwise

variable {k G : Type*}

variable [AddCommMonoid k] {a : G} {b : k}

theorem support_sum {k' G' : Type*} [DecidableEq G'] [AddCommMonoid k'] {f : SkewMonoidAlgebra k G}
    {g : G → k → SkewMonoidAlgebra k' G'} :
    (f.sum g).support ⊆ f.support.biUnion fun a ↦ (g a (f.coeff a)).support := by
  simp_rw [support, toFinsupp_sum']
  apply Finsupp.support_sum

