import Mathlib

variable {m : Type u} {n : Type v} {α : Type w}

variable [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m] [CommRing α]

variable (A : Matrix n n α) (b : n → α)

theorem cramer_transpose_row_self (i : n) : Aᵀ.cramer (A i) = Pi.single i A.det := by
  ext j
  rw [Matrix.cramer_apply, Pi.single_apply]
  split_ifs with h
  · -- i = j: this entry should be `A.det`
    subst h
    simp only [updateCol_transpose, det_transpose, updateRow_eq_self]
  · -- i ≠ j: this entry should be 0
    rw [updateCol_transpose, det_transpose]
    apply det_zero_of_row_eq h
    rw [updateRow_self, updateRow_ne (Ne.symm h)]

