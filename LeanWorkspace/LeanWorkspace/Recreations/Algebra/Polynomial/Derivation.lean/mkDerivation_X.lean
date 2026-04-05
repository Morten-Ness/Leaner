import Mathlib

variable {R A : Type*} [CommSemiring R]

variable [AddCommMonoid A] [Module R A] [Module (Polynomial R) A]

variable [IsScalarTower R (Polynomial R) A]

theorem mkDerivation_X (a : A) : Polynomial.mkDerivation R a X = a := by simp [Polynomial.mkDerivation_apply]

