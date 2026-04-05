import Mathlib

variable {ι α β : Type*}

variable [Semiring α] [LinearOrder α] [IsStrictOrderedRing α] [ExistsAddOfLE α]
  [AddCommMonoid β] [LinearOrder β] [IsOrderedCancelAddMonoid β]
  [Module α β] [PosSMulMono α β] {s : Finset ι} {σ : Perm ι} {f : ι → α} {g : ι → β}

theorem AntivaryOn.card_smul_sum_le_sum_smul_sum (hfg : AntivaryOn f g s) :
    #s • ∑ i ∈ s, f i • g i ≤ (∑ i ∈ s, f i) • ∑ i ∈ s, g i := hfg.dual_right.sum_smul_sum_le_card_smul_sum

