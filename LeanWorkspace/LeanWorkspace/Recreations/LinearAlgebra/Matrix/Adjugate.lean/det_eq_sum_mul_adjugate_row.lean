import Mathlib

variable {m : Type u} {n : Type v} {α : Type w}

variable [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m] [CommRing α]

theorem det_eq_sum_mul_adjugate_row (A : Matrix n n α) (i : n) :
    det A = ∑ j : n, A i j * Matrix.adjugate A j i := by
  haveI : Nonempty n := ⟨i⟩
  obtain ⟨n', hn'⟩ := Nat.exists_eq_succ_of_ne_zero (Fintype.card_ne_zero : Fintype.card n ≠ 0)
  obtain ⟨e⟩ := Fintype.truncEquivFinOfCardEq hn'
  let A' := reindex e e A
  suffices det A' = ∑ j : Fin n'.succ, A' (e i) j * Matrix.adjugate A' j (e i) by
    simp_rw [A', det_reindex_self, Matrix.adjugate_reindex, reindex_apply, submatrix_apply, ← e.sum_comp,
      Equiv.symm_apply_apply] at this
    exact this
  rw [det_succ_row A' (e i)]
  simp_rw [mul_assoc, mul_left_comm _ (A' _ _), ← Matrix.adjugate_fin_succ_eq_det_submatrix]

