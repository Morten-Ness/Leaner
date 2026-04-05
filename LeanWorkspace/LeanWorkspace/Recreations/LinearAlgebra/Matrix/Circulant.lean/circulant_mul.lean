import Mathlib

variable {α β n R : Type*}

theorem circulant_mul [NonUnitalNonAssocSemiring α] [Fintype n] [AddGroup n] (v w : n → α) :
    Matrix.circulant v * Matrix.circulant w = Matrix.circulant (Matrix.circulant v *ᵥ w) := by
  ext i j
  simp only [mul_apply, mulVec, Matrix.circulant_apply, dotProduct]
  refine Fintype.sum_equiv (Equiv.subRight j) _ _ ?_
  intro x
  simp only [Equiv.subRight_apply, sub_sub_sub_cancel_right]

