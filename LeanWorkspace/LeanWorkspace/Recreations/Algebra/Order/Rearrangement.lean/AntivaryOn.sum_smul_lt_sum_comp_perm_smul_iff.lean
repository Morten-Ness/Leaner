import Mathlib

variable {ι α β : Type*} [Semiring α] [LinearOrder α] [IsStrictOrderedRing α] [ExistsAddOfLE α]
  [AddCommMonoid β] [LinearOrder β] [IsOrderedCancelAddMonoid β] [Module α β]

variable [PosSMulStrictMono α β] {s : Finset ι} {σ : Perm ι} {f : ι → α} {g : ι → β}

theorem AntivaryOn.sum_smul_lt_sum_comp_perm_smul_iff (hfg : AntivaryOn f g s)
    (hσ : {x | σ x ≠ x} ⊆ s) :
    ∑ i ∈ s, f i • g i < ∑ i ∈ s, f (σ i) • g i ↔ ¬AntivaryOn (f ∘ σ) g s := by
  simp [← hfg.sum_comp_perm_smul_eq_sum_smul_iff hσ, eq_comm, lt_iff_le_and_ne,
    hfg.sum_smul_le_sum_comp_perm_smul hσ]

