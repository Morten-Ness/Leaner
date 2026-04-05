import Mathlib

variable {R : Type*} [CommRing R]

variable {K : Type*} [LieRing K] [LieAlgebra R K]

variable {L : Type*} [LieRing L] [LieAlgebra R L]

variable (ψ : L →ₗ⁅R⁆ LieDerivation R K K)

theorem projr_inr_apply {x : L} : LieAlgebra.SemiDirectSum.projr ψ (LieAlgebra.SemiDirectSum.inr ψ x) = x := by simp

