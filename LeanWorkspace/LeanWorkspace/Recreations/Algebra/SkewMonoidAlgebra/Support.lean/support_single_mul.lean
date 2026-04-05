import Mathlib

open scoped Pointwise

variable {k G : Type*}

variable [Monoid G] [Semiring k] [MulSemiringAction G k]

variable (f g : SkewMonoidAlgebra k G)

theorem support_single_mul [IsLeftCancelMul G] (r : k) (x : G)
    (hrx : ∀ y, r * x • y = 0 ↔ y = 0) :
    (single x r * f : SkewMonoidAlgebra k G).support = f.support.map (mulLeftEmbedding x) := by
  classical
  ext a
  simp [SkewMonoidAlgebra.support_single_mul_eq_image f (IsLeftRegular.all x) hrx]

