import Mathlib

open scoped Ring

variable {R : Type u} [CommRing R]

variable {n G : Type v} [DecidableEq n] [Fintype n]

variable {α β : Type v} [DecidableEq α]

variable {M : Matrix n n R}

theorem charpoly_sub_diagonal_degree_lt :
    (M.charpoly - ∏ i : n, (Polynomial.X - Polynomial.C (M i i))).degree < ↑(Fintype.card n - 1) := by
  rw [Matrix.charpoly, Matrix.det_apply', ← Finset.insert_erase (Finset.mem_univ (Equiv.refl n)),
    Finset.sum_insert (Finset.notMem_erase (Equiv.refl n) Finset.univ), add_comm]
  simp only [Matrix.charmatrix_apply_eq, one_mul, Equiv.Perm.sign_refl, id, Int.cast_one,
    Units.val_one, add_sub_cancel_right, Equiv.coe_refl]
  rw [← Polynomial.mem_degreeLT]
  apply Submodule.sum_mem (Polynomial.degreeLT R (Fintype.card n - 1))
  intro c hc; rw [← Polynomial.C_eq_intCast, C_mul']
  apply Submodule.smul_mem (Polynomial.degreeLT R (Fintype.card n - 1)) ↑↑(Equiv.Perm.sign c)
  rw [Polynomial.mem_degreeLT]
  apply lt_of_le_of_lt Polynomial.degree_le_natDegree _
  rw [Nat.cast_lt]
  apply lt_of_le_of_lt _ (Equiv.Perm.fixed_point_card_lt_of_ne_one (ne_of_mem_erase hc))
  apply le_trans (Polynomial.natDegree_prod_le Finset.univ fun i : n => Matrix.charmatrix M (c i) i) _
  rw [Finset.card_eq_sum_ones]; rw [Finset.sum_filter]; apply Finset.sum_le_sum
  intros
  apply Matrix.charmatrix_apply_natDegree_le

