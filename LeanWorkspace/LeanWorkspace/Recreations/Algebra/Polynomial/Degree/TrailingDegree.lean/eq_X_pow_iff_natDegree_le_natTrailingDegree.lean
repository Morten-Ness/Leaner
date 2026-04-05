import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b : R} {n m : ℕ}

variable [Semiring R] {p q : R[X]}

theorem eq_X_pow_iff_natDegree_le_natTrailingDegree (h₁ : p.Monic) :
    p = Polynomial.X ^ p.natDegree ↔ p.natDegree ≤ p.natTrailingDegree := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · nontriviality R
    rw [h, Polynomial.natTrailingDegree_X_pow, ← h]
  · ext n
    rw [coeff_X_pow]
    obtain hn | rfl | hn := lt_trichotomy n p.natDegree
    · rw [if_neg hn.ne, Polynomial.coeff_eq_zero_of_lt_natTrailingDegree (hn.trans_le h)]
    · simpa only [if_pos rfl] using h₁.leadingCoeff
    · rw [if_neg hn.ne', coeff_eq_zero_of_natDegree_lt hn]

