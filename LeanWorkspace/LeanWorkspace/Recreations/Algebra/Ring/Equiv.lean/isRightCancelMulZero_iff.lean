import Mathlib

variable {F α β R S S' : Type*}

variable {A B : Type*} [MulZeroClass A] [MulZeroClass B]

theorem isRightCancelMulZero_iff (e : A ≃* B) :
    IsRightCancelMulZero A ↔ IsRightCancelMulZero B where
  mp _ := RingEquiv.injective e.symm.isRightCancelMulZero _ (RingEquiv.map_zero _) (RingEquiv.map_mul _)
  mpr _ := RingEquiv.injective e.isRightCancelMulZero _ (RingEquiv.map_zero _) (RingEquiv.map_mul _)

