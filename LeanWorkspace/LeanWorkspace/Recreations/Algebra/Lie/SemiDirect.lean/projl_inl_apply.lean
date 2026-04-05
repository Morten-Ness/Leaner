import Mathlib

variable {R : Type*} [CommRing R]

variable {K : Type*} [LieRing K] [LieAlgebra R K]

variable {L : Type*} [LieRing L] [LieAlgebra R L]

variable (ψ : L →ₗ⁅R⁆ LieDerivation R K K)

theorem projl_inl_apply {x : K} : LieAlgebra.SemiDirectSum.projl ψ (LieAlgebra.SemiDirectSum.inl ψ x) = x := by simp

