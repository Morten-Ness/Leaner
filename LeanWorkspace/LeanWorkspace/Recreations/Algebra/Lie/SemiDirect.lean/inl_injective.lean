import Mathlib

variable {R : Type*} [CommRing R]

variable {K : Type*} [LieRing K] [LieAlgebra R K]

variable {L : Type*} [LieRing L] [LieAlgebra R L]

variable (ψ : L →ₗ⁅R⁆ LieDerivation R K K)

theorem inl_injective : Function.Injective (LieAlgebra.SemiDirectSum.inl ψ) := by intro; simp [LieAlgebra.SemiDirectSum.inl]

