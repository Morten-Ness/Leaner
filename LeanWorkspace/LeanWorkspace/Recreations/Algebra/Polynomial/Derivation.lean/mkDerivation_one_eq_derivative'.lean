import Mathlib

variable {R A : Type*} [CommSemiring R]

variable [AddCommMonoid A] [Module R A] [Module (Polynomial R) A]

variable [IsScalarTower R (Polynomial R) A]

theorem mkDerivation_one_eq_derivative' : Polynomial.mkDerivation R (1 : R[X]) = Polynomial.derivative' := by
  ext : 1
  simp [Polynomial.derivative']

