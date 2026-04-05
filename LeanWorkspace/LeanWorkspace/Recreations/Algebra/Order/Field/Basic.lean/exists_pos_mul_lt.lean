import Mathlib

variable {ι α β : Type*}

variable {α : Type*} [Semifield α] [LinearOrder α] [IsStrictOrderedRing α] {a b c d e : α}

theorem exists_pos_mul_lt {a : α} (h : 0 < a) (b : α) : ∃ c : α, 0 < c ∧ b * c < a := by
  have : 0 < a / max (b + 1) 1 := div_pos h (lt_max_iff.2 (Or.inr zero_lt_one))
  refine ⟨a / max (b + 1) 1, this, ?_⟩
  rw [← lt_div_iff₀ this, div_div_cancel₀ h.ne']
  exact lt_max_iff.2 (Or.inl <| lt_add_one _)

