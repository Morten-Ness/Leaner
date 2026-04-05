import Mathlib

variable {ι α β : Type*} [Semiring α] [LinearOrder α] [IsStrictOrderedRing α] [ExistsAddOfLE α]
  [AddCommMonoid β] [LinearOrder β] [IsOrderedCancelAddMonoid β] [Module α β]

variable [PosSMulMono α β] {s : Finset ι} {σ : Perm ι} {f : ι → α} {g : ι → β}

theorem AntivaryOn.sum_smul_le_sum_smul_comp_perm (hfg : AntivaryOn f g s)
    (hσ : {x | σ x ≠ x} ⊆ s) : ∑ i ∈ s, f i • g i ≤ ∑ i ∈ s, f i • g (σ i) := hfg.dual_right.sum_smul_comp_perm_le_sum_smul hσ

