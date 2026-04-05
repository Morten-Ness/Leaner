import Mathlib

variable {ι α β : Type*}

variable {α : Type*} [Semifield α] [LinearOrder α] [IsStrictOrderedRing α] {a b c d e : α}

theorem exists_pos_lt_mul {a : α} (h : 0 < a) (b : α) : ∃ c : α, 0 < c ∧ b < c * a := let ⟨c, hc₀, hc⟩ := exists_pos_mul_lt h b;
  ⟨c⁻¹, inv_pos.2 hc₀, by rwa [← div_eq_inv_mul, lt_div_iff₀ hc₀]⟩

