import Mathlib

variable (n p : Type*) (R : Type u₂) {𝕜 : Type*} [Field 𝕜]

variable [DecidableEq n] [DecidableEq p]

variable [CommRing R]

variable {R n} (i j : n)

variable [Fintype n]

theorem det_transvection_of_ne (h : i ≠ j) (c : R) : det (Matrix.transvection i j c) = 1 := by
  rw [← Matrix.updateRow_eq_transvection i j, det_updateRow_add_smul_self _ h, det_one]

