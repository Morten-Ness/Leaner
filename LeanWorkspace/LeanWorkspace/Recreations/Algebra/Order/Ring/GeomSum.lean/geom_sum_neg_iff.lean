import Mathlib

variable {R : Type*}

variable [Ring R]

variable [LinearOrder R] [IsStrictOrderedRing R] {n : ℕ} {x : R}

theorem geom_sum_neg_iff (hn : n ≠ 0) : ∑ i ∈ range n, x ^ i < 0 ↔ Even n ∧ x + 1 < 0 := by
  rw [← not_iff_not, not_lt, le_iff_lt_or_eq, eq_comm,
    or_congr (geom_sum_pos_iff hn) (geom_sum_eq_zero_iff_neg_one hn), ← Nat.not_even_iff_odd, ←
    add_eq_zero_iff_eq_neg, not_and, not_lt, le_iff_lt_or_eq, eq_comm, ← imp_iff_not_or, or_comm,
    and_comm, Decidable.and_or_imp, or_comm]

