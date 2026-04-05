import Mathlib

variable {m : Type u} {n : Type v} {α : Type w}

variable [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m] [CommRing α]

theorem adjugate_diagonal (v : n → α) :
    Matrix.adjugate (diagonal v) = diagonal fun i => ∏ j ∈ Finset.univ.erase i, v j := by
  ext i j
  simp only [Matrix.adjugate_def, Matrix.cramer_apply, diagonal_transpose, of_apply]
  obtain rfl | hij := eq_or_ne i j
  · rw [diagonal_apply_eq, diagonal_updateCol_single, det_diagonal,
      prod_update_of_mem (Finset.mem_univ _), sdiff_singleton_eq_erase, one_mul]
  · rw [diagonal_apply_ne _ hij]
    refine det_eq_zero_of_row_eq_zero j fun k => ?_
    obtain rfl | hjk := eq_or_ne k j
    · rw [updateCol_self, Pi.single_eq_of_ne' hij]
    · rw [updateCol_ne hjk, diagonal_apply_ne' _ hjk]

