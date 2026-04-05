import Mathlib

variable {ι α β : Type*}

variable [Semifield α] [LinearOrder α] [IsStrictOrderedRing α] [ExistsAddOfLE α]
  {s : Finset ι} {f : ι → α}

theorem pow_sum_div_card_le_sum_pow (hf : ∀ i ∈ s, 0 ≤ f i) (n : ℕ) :
    (∑ i ∈ s, f i) ^ (n + 1) / #s ^ n ≤ ∑ i ∈ s, f i ^ (n + 1) := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp
  rw [div_le_iff₀' (by positivity)]
  exact pow_sum_le_card_mul_sum_pow hf _

