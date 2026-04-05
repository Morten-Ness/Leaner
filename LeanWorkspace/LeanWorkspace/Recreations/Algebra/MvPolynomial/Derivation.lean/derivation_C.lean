import Mathlib

variable {σ R A : Type*} [CommSemiring R] [AddCommMonoid A] [Module R A]
  [Module (MvPolynomial σ R) A]

theorem derivation_C (D : Derivation R (MvPolynomial σ R) A) (a : R) : D (C a) = 0 := D.map_algebraMap a

