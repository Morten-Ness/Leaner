import Mathlib

variable {F α β R S S' : Type*}

variable {A B : Type*} [MulZeroClass A] [MulZeroClass B]

theorem isLeftCancelMulZero_iff (e : A ≃* B) : IsLeftCancelMulZero A ↔ IsLeftCancelMulZero B where
  mp _ := RingEquiv.injective e.symm.isLeftCancelMulZero _ (RingEquiv.map_zero _) (RingEquiv.map_mul _)
  mpr _ := RingEquiv.injective e.isLeftCancelMulZero _ (RingEquiv.map_zero _) (RingEquiv.map_mul _)

