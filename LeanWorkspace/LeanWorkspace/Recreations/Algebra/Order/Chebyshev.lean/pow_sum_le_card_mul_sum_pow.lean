import Mathlib

variable {ι α β : Type*}

variable [Semiring α] [LinearOrder α] [IsStrictOrderedRing α] [ExistsAddOfLE α]
  {s : Finset ι} {σ : Perm ι} {f g : ι → α}

theorem pow_sum_le_card_mul_sum_pow (hf : ∀ i ∈ s, 0 ≤ f i) :
    ∀ n, (∑ i ∈ s, f i) ^ (n + 1) ≤ (#s : α) ^ n * ∑ i ∈ s, f i ^ (n + 1)
  | 0 => by simp
  | n + 1 =>
    calc
      _ = (∑ i ∈ s, f i) ^ (n + 1) * ∑ i ∈ s, f i := by rw [pow_succ]
      _ ≤ (#s ^ n * ∑ i ∈ s, f i ^ (n + 1)) * ∑ i ∈ s, f i := by
        gcongr
        exacts [sum_nonneg hf, pow_sum_le_card_mul_sum_pow hf _]
      _ = #s ^ n * ((∑ i ∈ s, f i ^ (n + 1)) * ∑ i ∈ s, f i) := by rw [mul_assoc]
      _ ≤ #s ^ n * (#s * ∑ i ∈ s, f i ^ (n + 1) * f i) := by
        gcongr _ * ?_
        exact ((monovaryOn_self ..).pow_left₀ hf _).sum_mul_sum_le_card_mul_sum
      _ = _ := by simp_rw [← mul_assoc, ← pow_succ]

