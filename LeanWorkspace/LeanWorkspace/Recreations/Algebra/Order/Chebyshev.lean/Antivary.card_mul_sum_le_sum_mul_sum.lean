import Mathlib

variable {ι α β : Type*}

variable [Semiring α] [LinearOrder α] [IsStrictOrderedRing α] [ExistsAddOfLE α]
  {s : Finset ι} {σ : Perm ι} {f g : ι → α}

variable [Fintype ι]

theorem Antivary.card_mul_sum_le_sum_mul_sum (hfg : Antivary f g) :
    Fintype.card ι * ∑ i, f i * g i ≤ (∑ i, f i) * ∑ i, g i := (hfg.antivaryOn _).card_mul_sum_le_sum_mul_sum

