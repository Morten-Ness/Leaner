import Mathlib

variable {R : Type*} [CommRing R]

variable {K : Type*} [LieRing K] [LieAlgebra R K]

variable {L : Type*} [LieRing L] [LieAlgebra R L]

variable (ψ : L →ₗ⁅R⁆ LieDerivation R K K)

theorem projl_inr_apply {x : L} : LieAlgebra.SemiDirectSum.projl ψ (LieAlgebra.SemiDirectSum.inr ψ x) = 0 := by simp

