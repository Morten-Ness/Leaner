import Mathlib

variable {ι α β : Type*}

variable [Semiring α] [LinearOrder α] [IsStrictOrderedRing α] [ExistsAddOfLE α]
  [AddCommMonoid β] [LinearOrder β] [IsOrderedCancelAddMonoid β]
  [Module α β] [PosSMulMono α β] {s : Finset ι} {σ : Perm ι} {f : ι → α} {g : ι → β}

variable [Fintype ι]

theorem Antivary.card_smul_sum_le_sum_smul_sum (hfg : Antivary f g) :
    Fintype.card ι • ∑ i, f i • g i ≤ (∑ i, f i) • ∑ i, g i := (hfg.dual_right.monovaryOn _).sum_smul_sum_le_card_smul_sum

