import Mathlib

open scoped Ring Polynomial

variable {R : Type u} [CommRing R]

variable {n G : Type v} [DecidableEq n] [Fintype n]

variable {α β : Type v} [DecidableEq α]

variable {M : Matrix n n R}

theorem det_one_add_smul (r : R) (M : Matrix n n R) :
    Matrix.det (1 + r • M) =
      1 + Matrix.trace M * r + (Matrix.det (1 + (Polynomial.X : R[X]) • M.map Polynomial.C)).divX.divX.eval r * r ^ 2 := by
  simpa [eval_det, ← smul_eq_mul_diagonal] using congr_arg (eval r) (Matrix.det_one_add_X_smul M)

