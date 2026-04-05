import Mathlib

variable {ι F M N O G H : Type*}

variable [AddZeroClass M] [AddZeroClass N] {f : M → N} {g₁ g₂ : ι →₀ M}

theorem support_single_add_single_subset [DecidableEq ι] {f₁ f₂ : ι} {g₁ g₂ : M} :
    (single f₁ g₁ + single f₂ g₂).support ⊆ {f₁, f₂} := by
  refine subset_trans Finsupp.support_add <| union_subset_iff.mpr ⟨?_, ?_⟩ <;>
  exact subset_trans Finsupp.support_single_subset (by simp)

