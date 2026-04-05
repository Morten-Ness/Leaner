import Mathlib

variable {ι α β : Type*}

variable [Semiring α] [LinearOrder α] [IsStrictOrderedRing α] [ExistsAddOfLE α]
  {s : Finset ι} {σ : Perm ι} {f g : ι → α}

variable [Fintype ι]

theorem Monovary.sum_mul_sum_le_card_mul_sum (hfg : Monovary f g) :
    (∑ i, f i) * ∑ i, g i ≤ Fintype.card ι * ∑ i, f i * g i := (hfg.monovaryOn _).sum_mul_sum_le_card_mul_sum

