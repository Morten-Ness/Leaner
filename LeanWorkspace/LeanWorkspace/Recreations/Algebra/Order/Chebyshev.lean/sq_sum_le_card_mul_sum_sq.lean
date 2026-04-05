import Mathlib

variable {ι α β : Type*}

variable [Semiring α] [LinearOrder α] [IsStrictOrderedRing α] [ExistsAddOfLE α]
  {s : Finset ι} {σ : Perm ι} {f g : ι → α}

theorem sq_sum_le_card_mul_sum_sq : (∑ i ∈ s, f i) ^ 2 ≤ #s * ∑ i ∈ s, f i ^ 2 := by
  simp_rw [sq]
  exact (monovaryOn_self _ _).sum_mul_sum_le_card_mul_sum

