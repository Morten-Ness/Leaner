import Mathlib

variable {m n : Type*} [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m]

variable {R : Type v} [CommRing R]

theorem abs_det_reindex {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    (e₁ e₂ : m ≃ n) (A : Matrix m m R) :
    |Matrix.det (reindex e₁ e₂ A)| = |Matrix.det A| := Matrix.abs_det_submatrix_equiv_equiv e₁.symm e₂.symm A

