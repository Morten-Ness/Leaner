import Mathlib

variable {ι α β : Type*}

variable [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
  [AddCommGroup β] [LinearOrder β] [IsOrderedAddMonoid β] [Module α β]
  [IsStrictOrderedModule α β] {f : ι → α} {g : ι → β} {s : Set ι}

theorem monovaryOn_iff_forall_smul_nonneg :
    MonovaryOn f g s ↔ ∀ ⦃i⦄, i ∈ s → ∀ ⦃j⦄, j ∈ s → 0 ≤ (f j - f i) • (g j - g i) := by
  simp_rw [smul_nonneg_iff_pos_imp_nonneg, sub_pos, sub_nonneg, forall_and]
  exact (and_iff_right_of_imp MonovaryOn.symm).symm

