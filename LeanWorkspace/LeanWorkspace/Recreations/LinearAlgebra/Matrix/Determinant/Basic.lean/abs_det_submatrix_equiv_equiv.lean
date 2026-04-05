import Mathlib

variable {m n : Type*} [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m]

variable {R : Type v} [CommRing R]

theorem abs_det_submatrix_equiv_equiv {R : Type*}
    [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    (e₁ e₂ : n ≃ m) (A : Matrix m m R) :
    |(A.submatrix e₁ e₂).det| = |A.det| := by
  have hee : e₂ = e₁.trans (e₁.symm.trans e₂) := by ext; simp
  rw [hee]
  change |((A.submatrix id (e₁.symm.trans e₂)).submatrix e₁ e₁).det| = |A.det|
  rw [Matrix.det_submatrix_equiv_self, Matrix.det_permute', abs_mul, abs_unit_intCast, one_mul]

