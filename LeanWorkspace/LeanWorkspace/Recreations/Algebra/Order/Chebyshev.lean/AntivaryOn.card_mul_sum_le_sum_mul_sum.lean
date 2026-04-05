import Mathlib

variable {ι α β : Type*}

variable [Semiring α] [LinearOrder α] [IsStrictOrderedRing α] [ExistsAddOfLE α]
  {s : Finset ι} {σ : Perm ι} {f g : ι → α}

theorem AntivaryOn.card_mul_sum_le_sum_mul_sum (hfg : AntivaryOn f g s) :
    (#s : α) * ∑ i ∈ s, f i * g i ≤ (∑ i ∈ s, f i) * ∑ i ∈ s, g i := by
  rw [← nsmul_eq_mul]
  exact hfg.card_smul_sum_le_sum_smul_sum

