import Mathlib

open scoped Pointwise

variable {k G : Type*}

variable [Monoid G] [Semiring k] [MulSemiringAction G k]

variable (f g : SkewMonoidAlgebra k G)

variable [DecidableEq G]

theorem support_mul : (f * g).support ⊆ f.support * g.support := SkewMonoidAlgebra.support_sum.trans <| biUnion_subset.2 fun _x hx ↦
    SkewMonoidAlgebra.support_sum.trans <| biUnion_subset.2 fun _y hy ↦
      SkewMonoidAlgebra.support_single_subset.trans <| singleton_subset_iff.2 <| mem_image₂_of_mem hx hy

