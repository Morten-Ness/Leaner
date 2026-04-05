import Mathlib

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] [Semiring S] {p q r : R[X]}

theorem le_natDegree_of_ne_zero (h : coeff p n ≠ 0) : n ≤ natDegree p := by
  rw [← Nat.cast_le (α := WithBot ℕ), ← degree_eq_natDegree]
  · exact le_degree_of_ne_zero h
  · rintro rfl
    exact h rfl

