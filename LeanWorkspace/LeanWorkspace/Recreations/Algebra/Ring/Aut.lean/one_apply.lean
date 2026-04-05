import Mathlib

variable (R : Type*) [Mul R] [Add R]

theorem one_apply (x : R) : (1 : R ≃+* R) x = x := rfl

