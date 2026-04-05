import Mathlib

variable {R A : Type*} [CommSemiring R]

variable [AddCommMonoid A] [Module R A] [Module (Polynomial R) A]

theorem derivation_C (D : Derivation R R[X] A) (a : R) : D (C a) = 0 := D.map_algebraMap a

