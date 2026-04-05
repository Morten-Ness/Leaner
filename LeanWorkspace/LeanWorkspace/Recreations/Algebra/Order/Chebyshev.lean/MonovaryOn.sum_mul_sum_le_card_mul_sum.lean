import Mathlib

variable {ι α β : Type*}

variable [Semiring α] [LinearOrder α] [IsStrictOrderedRing α] [ExistsAddOfLE α]
  {s : Finset ι} {σ : Perm ι} {f g : ι → α}

theorem MonovaryOn.sum_mul_sum_le_card_mul_sum (hfg : MonovaryOn f g s) :
    (∑ i ∈ s, f i) * ∑ i ∈ s, g i ≤ #s * ∑ i ∈ s, f i * g i := by
  rw [← nsmul_eq_mul]
  exact hfg.sum_smul_sum_le_card_smul_sum

