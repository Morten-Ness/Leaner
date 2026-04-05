import Mathlib

variable (R : Type*) [CommRing R]

variable (L : Type*) [LieRing L] [LieAlgebra R L]

variable (M : Type*) [AddCommGroup M] [Module R M]

theorem mem_twoCochain_iff {c : L →ₗ[R] L →ₗ[R] M} : c ∈ LieModule.Cohomology.twoCochain R L M ↔ ∀ x, c x x = 0 := Iff.rfl

