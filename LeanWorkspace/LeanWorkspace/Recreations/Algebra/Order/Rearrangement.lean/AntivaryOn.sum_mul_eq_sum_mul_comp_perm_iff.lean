import Mathlib

variable {ι α β : Type*} [Semiring α] [LinearOrder α] [IsStrictOrderedRing α] [ExistsAddOfLE α]
  [AddCommMonoid β] [LinearOrder β] [IsOrderedCancelAddMonoid β] [Module α β]

variable {s : Finset ι} {σ : Perm ι} {f g : ι → α}

theorem AntivaryOn.sum_mul_eq_sum_mul_comp_perm_iff (hfg : AntivaryOn f g s)
    (hσ : {x | σ x ≠ x} ⊆ s) :
    ∑ i ∈ s, f i * g (σ i) = ∑ i ∈ s, f i * g i ↔ AntivaryOn f (g ∘ σ) s := hfg.sum_smul_comp_perm_eq_sum_smul_iff hσ

