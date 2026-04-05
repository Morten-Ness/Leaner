import Mathlib

variable {ι α β : Type*}

variable [Ring α] [LinearOrder α] [IsStrictOrderedRing α] {f g : ι → α} {s : Set ι}

theorem antivaryOn_iff_mul_rearrangement :
    AntivaryOn f g s ↔
      ∀ ⦃i⦄, i ∈ s → ∀ ⦃j⦄, j ∈ s → f i * g i + f j * g j ≤ f i * g j + f j * g i := by
  simp only [smul_eq_mul, antivaryOn_iff_smul_rearrangement]

