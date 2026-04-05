import Mathlib

variable {m n : Type*} [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m]

variable {R : Type v} [CommRing R]

theorem det_updateRow_sum (A : Matrix n n R) (j : n) (c : n → R) :
    (A.updateRow j (∑ k, (c k) • A k)).det = (c j) • A.det := by
  convert Matrix.det_updateRow_sum_aux A (Finset.univ.erase j) (Finset.univ.notMem_erase j) c (c j)
  rw [← Finset.univ.add_sum_erase _ (Finset.mem_univ j)]

