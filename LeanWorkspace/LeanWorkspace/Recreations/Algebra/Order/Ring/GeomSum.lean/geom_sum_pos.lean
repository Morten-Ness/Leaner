import Mathlib

variable {R : Type*}

variable [Semiring R] [PartialOrder R] [IsStrictOrderedRing R] {n : ℕ} {x : R}

theorem geom_sum_pos (hx : 0 ≤ x) (hn : n ≠ 0) : 0 < ∑ i ∈ range n, x ^ i := sum_pos' (fun _ _ => pow_nonneg hx _) ⟨0, mem_range.2 hn.bot_lt, by simp⟩

