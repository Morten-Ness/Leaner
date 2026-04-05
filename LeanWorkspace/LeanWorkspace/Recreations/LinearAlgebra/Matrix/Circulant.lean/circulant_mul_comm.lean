import Mathlib

variable {α β n R : Type*}

theorem circulant_mul_comm [CommMagma α] [AddCommMonoid α] [Fintype n] [AddCommGroup n]
    (v w : n → α) : Matrix.circulant v * Matrix.circulant w = Matrix.circulant w * Matrix.circulant v := by
  ext i j
  simp only [mul_apply, Matrix.circulant_apply]
  refine Fintype.sum_equiv ((Equiv.subLeft i).trans (Equiv.addRight j)) _ _ ?_
  intro x
  simp only [Equiv.trans_apply, Equiv.subLeft_apply, Equiv.coe_addRight, add_sub_cancel_right,
    mul_comm]
  congr 2
  abel

