import Mathlib

variable {σ R A : Type*} [CommSemiring R] [AddCommMonoid A] [Module R A]
  [Module (MvPolynomial σ R) A]

theorem derivation_C_mul (D : Derivation R (MvPolynomial σ R) A) (a : R) (f : MvPolynomial σ R) :
    C (σ := σ) a • D f = a • D f := by
  have : C (σ := σ) a • D f = D (C a * f) := by simp
  rw [this, C_mul', D.map_smul]

