import Mathlib

variable {m n : Type*} [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m]

variable {R : Type v} [CommRing R]

theorem det_apply' (M : Matrix n n R) : M.det = ∑ σ : Equiv.Perm n, ε σ * ∏ i, M (σ i) i := by
  simp [Matrix.det_apply, Units.smul_def]

