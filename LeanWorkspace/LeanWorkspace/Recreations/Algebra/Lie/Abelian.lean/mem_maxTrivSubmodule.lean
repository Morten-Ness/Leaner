import Mathlib

variable (R : Type u) (L : Type v) (M : Type w) (N : Type w₁)

variable [CommRing R] [LieRing L] [LieAlgebra R L]

variable [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable [AddCommGroup N] [Module R N] [LieRingModule L N] [LieModule R L N]

theorem mem_maxTrivSubmodule (m : M) : m ∈ LieModule.maxTrivSubmodule R L M ↔ ∀ x : L, ⁅x, m⁆ = 0 := Iff.rfl

