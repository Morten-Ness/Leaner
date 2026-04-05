import Mathlib

variable {ι α β : Type*} [Semiring α] [LinearOrder α] [IsStrictOrderedRing α] [ExistsAddOfLE α]
  [AddCommMonoid β] [LinearOrder β] [IsOrderedCancelAddMonoid β] [Module α β]

variable [PosSMulMono α β] {s : Finset ι} {σ : Perm ι} {f : ι → α} {g : ι → β}

theorem MonovaryOn.sum_comp_perm_smul_le_sum_smul (hfg : MonovaryOn f g s)
    (hσ : {x | σ x ≠ x} ⊆ s) : ∑ i ∈ s, f (σ i) • g i ≤ ∑ i ∈ s, f i • g i := by
  convert hfg.sum_smul_comp_perm_le_sum_smul
    (show { x | σ⁻¹ x ≠ x } ⊆ s by simp [set_support_symm_eq, hσ]) using 1
  exact σ.sum_comp' s (fun i j ↦ f i • g j) hσ

