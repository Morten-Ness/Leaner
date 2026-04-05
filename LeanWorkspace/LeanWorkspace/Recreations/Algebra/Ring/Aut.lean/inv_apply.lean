import Mathlib

variable (R : Type*) [Mul R] [Add R]

theorem inv_apply (f : R ≃+* R) (x : R) : f⁻¹ x = f.symm x := rfl

