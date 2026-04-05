import Mathlib

variable {ι α β : Type*}

variable [Semifield α] [LinearOrder α] [IsStrictOrderedRing α] [ExistsAddOfLE α]
  {s : Finset ι} {f : ι → α}

theorem sum_div_card_sq_le_sum_sq_div_card :
    ((∑ i ∈ s, f i) / #s) ^ 2 ≤ (∑ i ∈ s, f i ^ 2) / #s := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp
  rw [div_pow, div_le_div_iff₀ (by positivity) (by positivity), sq (#s : α), mul_left_comm,
    ← mul_assoc]
  exact mul_le_mul_of_nonneg_right sq_sum_le_card_mul_sum_sq (by positivity)

