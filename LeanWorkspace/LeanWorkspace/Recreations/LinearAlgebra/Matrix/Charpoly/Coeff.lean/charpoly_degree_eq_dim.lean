import Mathlib

open scoped Ring

variable {R : Type u} [CommRing R]

variable {n G : Type v} [DecidableEq n] [Fintype n]

variable {α β : Type v} [DecidableEq α]

variable {M : Matrix n n R}

theorem charpoly_degree_eq_dim [Nontrivial R] (M : Matrix n n R) :
    M.charpoly.degree = Fintype.card n := by
  by_cases h : Fintype.card n = 0
  · rw [h]
    unfold Matrix.charpoly
    rw [Matrix.det_eq_one_of_card_eq_zero]
    · simp
    · assumption
  rw [← sub_add_cancel M.charpoly (∏ i : n, (Polynomial.X - Polynomial.C (M i i)))]
  -- Porting note: added `↑` in front of `Fintype.card n`
  have h1 : (∏ i : n, (Polynomial.X - Polynomial.C (M i i))).degree = ↑(Fintype.card n) := by
    rw [degree_eq_iff_natDegree_eq_of_pos (Nat.pos_of_ne_zero h), natDegree_prod']
    · simp_rw [natDegree_X_sub_C]
      rw [← Finset.card_univ, sum_const, smul_eq_mul, mul_one]
    simp_rw [(Polynomial.monic_X_sub_C _).leadingCoeff]
    simp
  rw [degree_add_eq_right_of_degree_lt]
  · exact h1
  rw [h1]
  apply lt_trans (Matrix.charpoly_sub_diagonal_degree_lt M)
  rw [Nat.cast_lt]
  lia

