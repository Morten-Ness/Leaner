import Mathlib

open scoped Pointwise

variable {k G : Type*}

variable [Monoid G] [Semiring k] [MulSemiringAction G k]

variable (f g : SkewMonoidAlgebra k G)

variable [DecidableEq G]

theorem support_mul_single_subset (r : k) (a : G) :
    (f * single a r).support ⊆ Finset.image (· * a) f.support := (SkewMonoidAlgebra.support_mul _ _).trans <| (Finset.image₂_subset_left SkewMonoidAlgebra.support_single_subset).trans <| by
    rw [Finset.image₂_singleton_right]

