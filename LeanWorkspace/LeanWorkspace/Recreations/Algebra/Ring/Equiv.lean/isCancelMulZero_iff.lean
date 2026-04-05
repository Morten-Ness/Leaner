import Mathlib

variable {F α β R S S' : Type*}

variable {A B : Type*} [MulZeroClass A] [MulZeroClass B]

theorem isCancelMulZero_iff (e : A ≃* B) : IsCancelMulZero A ↔ IsCancelMulZero B where
  mp _ := RingEquiv.injective e.symm.isCancelMulZero _ (RingEquiv.map_zero _) (RingEquiv.map_mul _)
  mpr _ := RingEquiv.injective e.isCancelMulZero _ (RingEquiv.map_zero _) (RingEquiv.map_mul _)

