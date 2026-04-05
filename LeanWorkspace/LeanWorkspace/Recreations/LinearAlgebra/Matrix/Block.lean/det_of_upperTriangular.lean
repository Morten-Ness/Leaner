import Mathlib

variable {α β m n o : Type*} {m' n' : α → Type*}

variable {R : Type v} {M N : Matrix m m R} {b : m → α}

variable [CommRing R] [DecidableEq m] [Fintype m] [DecidableEq n] [Fintype n]

theorem det_of_upperTriangular [LinearOrder m] (h : M.BlockTriangular id) :
    M.det = ∏ i : m, M i i := by
  haveI : DecidableEq R := Classical.decEq _
  simp_rw [h.det, image_id, Matrix.det_toSquareBlock_id]

