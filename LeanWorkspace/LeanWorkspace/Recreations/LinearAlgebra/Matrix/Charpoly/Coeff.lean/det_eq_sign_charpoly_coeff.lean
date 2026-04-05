import Mathlib

variable {R : Type u} [CommRing R]

variable {n G : Type v} [DecidableEq n] [Fintype n]

variable {α β : Type v} [DecidableEq α]

variable {M : Matrix n n R}

theorem det_eq_sign_charpoly_coeff (M : Matrix n n R) :
    M.det = (-1) ^ Fintype.card n * M.charpoly.coeff 0 := by
  rw [coeff_zero_eq_eval_zero, charpoly, eval_det, matPolyEquiv_charmatrix, ← det_smul]
  simp

