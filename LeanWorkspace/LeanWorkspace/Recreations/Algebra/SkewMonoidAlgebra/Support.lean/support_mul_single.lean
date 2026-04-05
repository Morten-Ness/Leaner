import Mathlib

open scoped Pointwise

variable {k G : Type*}

variable [Monoid G] [Semiring k] [MulSemiringAction G k]

variable (f g : SkewMonoidAlgebra k G)

theorem support_mul_single [IsRightCancelMul G] (r : k) (x : G)
   (hrx : ∀ g : G, ∀ y, y * g • r = 0 ↔ y = 0) :
    (f * single x r).support = f.support.map (mulRightEmbedding x) := by
  classical
  ext a
  simp [SkewMonoidAlgebra.support_mul_single_eq_image f (IsRightRegular.all x) hrx]

