import Mathlib

variable {m n : Type*} [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m]

variable {R : Type v} [CommRing R]

theorem det_updateCol_sum (A : Matrix n n R) (j : n) (c : n → R) :
    (A.updateCol j (fun k ↦ ∑ i, (c i) • A k i)).det = (c j) • A.det := by
  rw [← Matrix.det_transpose, ← updateRow_transpose, ← Matrix.det_transpose A]
  convert Matrix.det_updateRow_sum A.transpose j c
  simp only [smul_eq_mul, Finset.sum_apply, Pi.smul_apply, transpose_apply]

