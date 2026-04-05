import Mathlib

open scoped Ring Polynomial

variable {R : Type u} [CommRing R]

variable {n G : Type v} [DecidableEq n] [Fintype n]

variable {α β : Type v} [DecidableEq α]

variable {M : Matrix n n R}

theorem derivative_det_one_add_X_smul (M : Matrix n n R) :
    (derivative <| Matrix.det (1 + (Polynomial.X : R[X]) • M.map Polynomial.C)).eval 0 = Matrix.trace M := by
  let e := Matrix.reindexLinearEquiv R R (Fintype.equivFin n) (Fintype.equivFin n)
  rw [← Matrix.det_reindexLinearEquiv_self R[X] (Fintype.equivFin n)]
  convert Matrix.derivative_det_one_add_X_smul_aux (e M)
  · ext; simp [map_add, e]
  · delta Matrix.trace
    rw [← (Fintype.equivFin n).symm.sum_comp]
    simp_rw [e, reindexLinearEquiv_apply, reindex_apply, Matrix.diag_apply, submatrix_apply]

