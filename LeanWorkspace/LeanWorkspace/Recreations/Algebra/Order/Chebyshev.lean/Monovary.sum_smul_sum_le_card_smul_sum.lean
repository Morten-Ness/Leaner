import Mathlib

variable {ι α β : Type*}

variable [Semiring α] [LinearOrder α] [IsStrictOrderedRing α] [ExistsAddOfLE α]
  [AddCommMonoid β] [LinearOrder β] [IsOrderedCancelAddMonoid β]
  [Module α β] [PosSMulMono α β] {s : Finset ι} {σ : Perm ι} {f : ι → α} {g : ι → β}

variable [Fintype ι]

theorem Monovary.sum_smul_sum_le_card_smul_sum (hfg : Monovary f g) :
    (∑ i, f i) • ∑ i, g i ≤ Fintype.card ι • ∑ i, f i • g i := (hfg.monovaryOn _).sum_smul_sum_le_card_smul_sum

