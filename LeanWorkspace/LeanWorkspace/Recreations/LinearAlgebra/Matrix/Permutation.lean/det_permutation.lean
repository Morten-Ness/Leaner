import Mathlib

variable {n R : Type*} [DecidableEq n] (σ τ : Perm n)

variable [Fintype n]

theorem det_permutation [CommRing R] : det (σ.permMatrix R) = Equiv.Perm.sign σ := by
  rw [← Matrix.mul_one (σ.permMatrix R), PEquiv.toMatrix_toPEquiv_mul,
    det_permute, det_one, mul_one]

