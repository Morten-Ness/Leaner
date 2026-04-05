import Mathlib

variable {R : Type*} [Semiring R]

theorem mulRight_symm_apply (u : Rˣ) (x : R) : (AddAut.mulRight u).symm x = x * u⁻¹ := rfl

