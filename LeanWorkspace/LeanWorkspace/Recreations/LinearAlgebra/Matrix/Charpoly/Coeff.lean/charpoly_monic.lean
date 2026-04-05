import Mathlib

variable {R : Type u} [CommRing R]

variable {n G : Type v} [DecidableEq n] [Fintype n]

variable {α β : Type v} [DecidableEq α]

variable {M : Matrix n n R}

theorem charpoly_monic (M : Matrix n n R) : M.charpoly.Monic := by
  nontriviality R
  by_cases h : Fintype.card n = 0
  · rw [charpoly, det_eq_one_of_card_eq_zero h]
    apply monic_one
  have mon : (∏ i : n, (X - C (M i i))).Monic := by
    apply monic_prod_of_monic Finset.univ fun i : n => X - C (M i i)
    simp [monic_X_sub_C]
  rw [← sub_add_cancel (∏ i : n, (X - C (M i i))) M.charpoly] at mon
  rw [Monic] at *
  rwa [leadingCoeff_add_of_degree_lt] at mon
  rw [Matrix.charpoly_degree_eq_dim]
  rw [← neg_sub]
  rw [degree_neg]
  apply lt_trans (Matrix.charpoly_sub_diagonal_degree_lt M)
  rw [Nat.cast_lt]
  lia

