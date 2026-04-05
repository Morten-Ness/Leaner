import Mathlib

variable {R A : Type*} [CommSemiring R]

variable [AddCommMonoid A] [Module R A] [Module (Polynomial R) A]

theorem C_smul_derivation_apply (D : Derivation R R[X] A) (a : R) (f : R[X]) :
    C a • D f = a • D f := by
  have : C a • D f = D (C a * f) := by simp
  rw [this, C_mul', D.map_smul]

