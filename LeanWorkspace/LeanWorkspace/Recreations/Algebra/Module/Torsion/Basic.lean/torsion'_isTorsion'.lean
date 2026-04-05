import Mathlib

variable {R M : Type*}

variable [CommSemiring R] [AddCommMonoid M] [Module R M]

variable (S : Type*) [CommMonoid S] [DistribMulAction S M] [SMulCommClass S R M]

theorem torsion'_isTorsion' : IsTorsion' (Submodule.torsion' R M S) S := fun ⟨_, ⟨a, h⟩⟩ => ⟨a, Subtype.ext h⟩

