import Mathlib

open scoped Ring

variable {R : Type u} [CommRing R]

variable {n G : Type v} [DecidableEq n] [Fintype n]

variable {α β : Type v} [DecidableEq α]

variable {M : Matrix n n R}

theorem charpoly_monic (M : Matrix n n R) : M.charpoly.Monic := by
  nontriviality R
  by_cases h : Fintype.card n = 0
  · rw [Matrix.charpoly, Matrix.det_eq_one_of_card_eq_zero h]
    apply Polynomial.monic_one
  have mon : (∏ i : n, (Polynomial.X - Polynomial.C (M i i))).Monic := by
    apply Polynomial.monic_prod_of_monic Finset.univ fun i : n => Polynomial.X - Polynomial.C (M i i)
    simp [Polynomial.monic_X_sub_C]
  rw [← sub_add_cancel (∏ i : n, (Polynomial.X - Polynomial.C (M i i))) M.charpoly] at mon
  rw [Polynomial.Monic] at *
  rwa [Polynomial.leadingCoeff_add_of_degree_lt] at mon
  rw [Matrix.charpoly_degree_eq_dim]
  rw [← neg_sub]
  rw [Polynomial.degree_neg]
  apply lt_trans (Matrix.charpoly_sub_diagonal_degree_lt M)
  rw [Nat.cast_lt]
  lia

