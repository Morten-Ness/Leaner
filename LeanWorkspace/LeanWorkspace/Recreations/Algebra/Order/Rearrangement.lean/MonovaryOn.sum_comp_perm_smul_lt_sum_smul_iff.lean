import Mathlib

variable {ι α β : Type*} [Semiring α] [LinearOrder α] [IsStrictOrderedRing α] [ExistsAddOfLE α]
  [AddCommMonoid β] [LinearOrder β] [IsOrderedCancelAddMonoid β] [Module α β]

variable [PosSMulStrictMono α β] {s : Finset ι} {σ : Perm ι} {f : ι → α} {g : ι → β}

theorem MonovaryOn.sum_comp_perm_smul_lt_sum_smul_iff (hfg : MonovaryOn f g s)
    (hσ : {x | σ x ≠ x} ⊆ s) :
    ∑ i ∈ s, f (σ i) • g i < ∑ i ∈ s, f i • g i ↔ ¬MonovaryOn (f ∘ σ) g s := by
  simp [← hfg.sum_comp_perm_smul_eq_sum_smul_iff hσ, lt_iff_le_and_ne,
    hfg.sum_comp_perm_smul_le_sum_smul hσ]

