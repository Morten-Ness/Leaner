import Mathlib

variable (R : Type*) [Mul R] [Add R]

theorem one_eq_refl : (1 : R ≃+* R) = RingEquiv.refl R := rfl

