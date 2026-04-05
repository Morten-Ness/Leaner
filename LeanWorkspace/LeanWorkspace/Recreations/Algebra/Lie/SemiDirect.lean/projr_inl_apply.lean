import Mathlib

variable {R : Type*} [CommRing R]

variable {K : Type*} [LieRing K] [LieAlgebra R K]

variable {L : Type*} [LieRing L] [LieAlgebra R L]

variable (ψ : L →ₗ⁅R⁆ LieDerivation R K K)

theorem projr_inl_apply {x : K} : LieAlgebra.SemiDirectSum.projr ψ (LieAlgebra.SemiDirectSum.inl ψ x) = 0 := by simp

