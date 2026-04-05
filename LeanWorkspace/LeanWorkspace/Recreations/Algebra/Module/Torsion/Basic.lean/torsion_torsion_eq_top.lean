import Mathlib

variable {R M : Type*}

variable [CommSemiring R] [AddCommMonoid M] [Module R M]

variable (S : Type*) [CommMonoid S] [DistribMulAction S M] [SMulCommClass S R M]

theorem torsion_torsion_eq_top : torsion R (torsion R M) = ⊤ := Submodule.torsion'_torsion'_eq_top R⁰

