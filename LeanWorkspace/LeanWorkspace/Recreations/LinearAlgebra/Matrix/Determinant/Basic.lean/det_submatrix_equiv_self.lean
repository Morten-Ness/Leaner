import Mathlib

variable {m n : Type*} [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m]

variable {R : Type v} [CommRing R]

theorem det_submatrix_equiv_self (e : n ≃ m) (A : Matrix m m R) :
    Matrix.det (A.submatrix e e) = Matrix.det A := by
  rw [Matrix.det_apply', Matrix.det_apply']
  apply Fintype.sum_equiv (Equiv.permCongr e)
  intro σ
  rw [Equiv.Perm.sign_permCongr e σ]
  congr 1
  apply Fintype.prod_equiv e
  intro i
  rw [Equiv.permCongr_apply, Equiv.symm_apply_apply, submatrix_apply]

