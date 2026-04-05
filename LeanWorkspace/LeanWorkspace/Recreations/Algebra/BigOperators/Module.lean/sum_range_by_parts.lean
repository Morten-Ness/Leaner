import Mathlib

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] (f : ℕ → R) (g : ℕ → M) {m n : ℕ}

theorem sum_range_by_parts :
    ∑ i ∈ range n, f i • g i =
      f (n - 1) • G n - ∑ i ∈ range (n - 1), (f (i + 1) - f i) • G (i + 1) := by
  by_cases hn : n = 0
  · simp [hn]
  · rw [range_eq_Ico, Finset.sum_Ico_by_parts f g (Nat.pos_of_ne_zero hn), sum_range_zero, smul_zero,
      sub_zero, range_eq_Ico]

