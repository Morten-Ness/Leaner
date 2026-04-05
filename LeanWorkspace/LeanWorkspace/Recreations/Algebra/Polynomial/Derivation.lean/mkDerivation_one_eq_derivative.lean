import Mathlib

variable {R A : Type*} [CommSemiring R]

variable [AddCommMonoid A] [Module R A] [Module (Polynomial R) A]

variable [IsScalarTower R (Polynomial R) A]

theorem mkDerivation_one_eq_derivative (f : R[X]) : Polynomial.mkDerivation R (1 : R[X]) f = derivative f := by
  rw [Polynomial.mkDerivation_one_eq_derivative']
  rfl

