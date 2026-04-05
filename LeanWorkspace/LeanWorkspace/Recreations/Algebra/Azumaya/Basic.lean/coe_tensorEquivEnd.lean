import Mathlib

open scoped TensorProduct

variable (R A B : Type*) [CommSemiring R] [Ring A] [Ring B] [Algebra R A] [Algebra R B]

theorem coe_tensorEquivEnd : tensorEquivEnd R = AlgHom.mulLeftRight R R := by
  ext; simp

