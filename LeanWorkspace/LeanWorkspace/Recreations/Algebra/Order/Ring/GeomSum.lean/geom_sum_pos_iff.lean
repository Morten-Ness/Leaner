import Mathlib

variable {R : Type*}

variable [Ring R]

variable [LinearOrder R] [IsStrictOrderedRing R] {n : ℕ} {x : R}

theorem geom_sum_pos_iff (hn : n ≠ 0) : 0 < ∑ i ∈ range n, x ^ i ↔ Odd n ∨ 0 < x + 1 := by
  refine ⟨fun h => ?_, ?_⟩
  · rw [or_iff_not_imp_left, ← not_le, Nat.not_odd_iff_even]
    refine fun hn hx => h.not_ge ?_
    simpa [if_pos hn] using geom_sum_alternating_of_le_neg_one hx n
  · rintro (hn | hx')
    · exact geom_sum_pos hn
    · exact geom_sum_pos' hx' hn

