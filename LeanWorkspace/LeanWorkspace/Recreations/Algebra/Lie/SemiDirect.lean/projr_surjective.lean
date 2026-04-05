import Mathlib

variable {R : Type*} [CommRing R]

variable {K : Type*} [LieRing K] [LieAlgebra R K]

variable {L : Type*} [LieRing L] [LieAlgebra R L]

variable (ψ : L →ₗ⁅R⁆ LieDerivation R K K)

theorem projr_surjective : Function.Surjective (LieAlgebra.SemiDirectSum.projr ψ) := fun x ↦ ⟨LieAlgebra.SemiDirectSum.inr ψ x, by simp⟩

