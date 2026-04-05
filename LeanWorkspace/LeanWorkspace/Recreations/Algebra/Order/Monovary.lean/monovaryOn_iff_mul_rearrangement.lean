import Mathlib

variable {ι α β : Type*}

variable [Ring α] [LinearOrder α] [IsStrictOrderedRing α] {f g : ι → α} {s : Set ι}

theorem monovaryOn_iff_mul_rearrangement :
    MonovaryOn f g s ↔
      ∀ ⦃i⦄, i ∈ s → ∀ ⦃j⦄, j ∈ s → f i * g j + f j * g i ≤ f i * g i + f j * g j := by
  simp only [smul_eq_mul, monovaryOn_iff_smul_rearrangement]

