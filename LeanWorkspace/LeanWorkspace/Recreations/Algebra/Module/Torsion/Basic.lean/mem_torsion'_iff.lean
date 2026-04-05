import Mathlib

variable {R M : Type*}

variable [CommSemiring R] [AddCommMonoid M] [Module R M]

variable (S : Type*) [CommMonoid S] [DistribMulAction S M] [SMulCommClass S R M]

theorem mem_torsion'_iff (x : M) : x ∈ Submodule.torsion' R M S ↔ ∃ a : S, a • x = 0 := Iff.rfl

