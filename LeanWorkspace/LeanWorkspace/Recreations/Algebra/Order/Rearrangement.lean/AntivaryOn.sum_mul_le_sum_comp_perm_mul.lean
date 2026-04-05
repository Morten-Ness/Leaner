import Mathlib

variable {ι α β : Type*} [Semiring α] [LinearOrder α] [IsStrictOrderedRing α] [ExistsAddOfLE α]
  [AddCommMonoid β] [LinearOrder β] [IsOrderedCancelAddMonoid β] [Module α β]

variable {s : Finset ι} {σ : Perm ι} {f g : ι → α}

theorem AntivaryOn.sum_mul_le_sum_comp_perm_mul (hfg : AntivaryOn f g s)
    (hσ : {x | σ x ≠ x} ⊆ s) : ∑ i ∈ s, f i * g i ≤ ∑ i ∈ s, f (σ i) * g i := hfg.sum_smul_le_sum_comp_perm_smul hσ

