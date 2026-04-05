import Mathlib

variable {n R : Type*} [DecidableEq n] (σ τ : Perm n)

variable [Fintype n]

theorem permMatrix_mulVec {v : n → R} [CommRing R] :
    σ.permMatrix R *ᵥ v = v ∘ σ := by
  ext j
  simp [mulVec_eq_sum, Pi.single, Function.update, Equiv.eq_symm_apply]

