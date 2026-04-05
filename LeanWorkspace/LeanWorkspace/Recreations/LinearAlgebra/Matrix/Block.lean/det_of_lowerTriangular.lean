import Mathlib

variable {α β m n o : Type*} {m' n' : α → Type*}

variable {R : Type v} {M N : Matrix m m R} {b : m → α}

variable [CommRing R] [DecidableEq m] [Fintype m] [DecidableEq n] [Fintype n]

theorem det_of_lowerTriangular [LinearOrder m] (M : Matrix m m R) (h : M.BlockTriangular toDual) :
    M.det = ∏ i : m, M i i := by
  rw [← det_transpose]
  exact Matrix.det_of_upperTriangular h.transpose

