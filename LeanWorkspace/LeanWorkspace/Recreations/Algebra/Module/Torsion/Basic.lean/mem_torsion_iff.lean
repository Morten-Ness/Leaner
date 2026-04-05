import Mathlib

variable {R M : Type*}

variable [CommSemiring R] [AddCommMonoid M] [Module R M]

variable (S : Type*) [CommMonoid S] [DistribMulAction S M] [SMulCommClass S R M]

theorem mem_torsion_iff (x : M) : x ∈ torsion R M ↔ ∃ a : R⁰, a • x = 0 := Iff.rfl

