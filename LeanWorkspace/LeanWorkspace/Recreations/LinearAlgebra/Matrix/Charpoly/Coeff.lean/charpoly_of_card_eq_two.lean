import Mathlib

open scoped Ring

variable {R : Type u} [CommRing R]

variable {n G : Type v} [DecidableEq n] [Fintype n]

variable {α β : Type v} [DecidableEq α]

variable {M : Matrix n n R}

theorem charpoly_of_card_eq_two [Nontrivial R] (hn : Fintype.card n = 2) :
    M.charpoly = Polynomial.X ^ 2 - Polynomial.C M.trace * Polynomial.X + Polynomial.C M.det := by
  have : Nonempty n := by rw [← Fintype.card_pos_iff]; lia
  ext i
  by_cases hi : i ∈ Finset.range 3
  · fin_cases hi
    · simp [Matrix.det_eq_sign_charpoly_coeff, hn]
    · simp [Matrix.trace_eq_neg_charpoly_coeff, hn]
    · simpa [leadingCoeff, charpoly_natDegree_eq_dim, hn, coeff_X] using
        M.charpoly_monic.leadingCoeff
  · rw [Finset.mem_range, not_lt, Nat.succ_le_iff] at hi
    suffices M.charpoly.coeff i = 0 by
      simpa [show i ≠ 2 by lia, show 1 ≠ i by lia, show i ≠ 0 by lia, coeff_X, coeff_C]
    apply coeff_eq_zero_of_natDegree_lt
    simpa [charpoly_natDegree_eq_dim, hn] using hi

