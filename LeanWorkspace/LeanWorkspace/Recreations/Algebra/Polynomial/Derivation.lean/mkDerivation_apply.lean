import Mathlib

variable {R A : Type*} [CommSemiring R]

variable [AddCommMonoid A] [Module R A] [Module (Polynomial R) A]

variable [IsScalarTower R (Polynomial R) A]

theorem mkDerivation_apply (a : A) (f : R[X]) :
    Polynomial.mkDerivation R a f = derivative f • a := by
  rfl

