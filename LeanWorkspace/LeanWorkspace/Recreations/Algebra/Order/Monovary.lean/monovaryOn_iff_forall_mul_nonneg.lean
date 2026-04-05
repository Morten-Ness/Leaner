import Mathlib

variable {ι α β : Type*}

variable [Ring α] [LinearOrder α] [IsStrictOrderedRing α] {f g : ι → α} {s : Set ι}

theorem monovaryOn_iff_forall_mul_nonneg :
    MonovaryOn f g s ↔ ∀ ⦃i⦄, i ∈ s → ∀ ⦃j⦄, j ∈ s → 0 ≤ (f j - f i) * (g j - g i) := by
  simp only [smul_eq_mul, monovaryOn_iff_forall_smul_nonneg]

