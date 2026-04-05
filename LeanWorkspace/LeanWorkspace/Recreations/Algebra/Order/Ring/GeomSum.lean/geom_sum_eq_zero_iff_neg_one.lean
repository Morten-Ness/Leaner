import Mathlib

variable {R : Type*}

variable [Ring R]

variable [LinearOrder R] [IsStrictOrderedRing R] {n : ℕ} {x : R}

theorem geom_sum_eq_zero_iff_neg_one (hn : n ≠ 0) : ∑ i ∈ range n, x ^ i = 0 ↔ x = -1 ∧ Even n := by
  refine ⟨fun h => ?_, @fun ⟨h, hn⟩ => by simp only [h, hn, neg_one_geom_sum, if_true]⟩
  contrapose! h
  have hx := eq_or_ne x (-1)
  rcases hx with hx | hx
  · rw [hx, neg_one_geom_sum]
    simp only [h hx, ite_false, ne_eq, one_ne_zero, not_false_eq_true]
  · exact geom_sum_ne_zero hx hn

