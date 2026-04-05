import Mathlib

variable {n R : Type*} [DecidableEq n] (σ τ : Perm n)

variable [Fintype n]

theorem vecMul_permMatrix {v : n → R} [CommRing R] :
    v ᵥ* σ.permMatrix R = v ∘ σ.symm := by
  ext j
  simp [vecMul_eq_sum, Pi.single, Function.update, ← Equiv.symm_apply_eq]

