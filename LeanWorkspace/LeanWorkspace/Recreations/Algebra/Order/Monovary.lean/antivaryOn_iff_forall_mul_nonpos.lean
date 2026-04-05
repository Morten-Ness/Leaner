import Mathlib

variable {ι α β : Type*}

variable [Ring α] [LinearOrder α] [IsStrictOrderedRing α] {f g : ι → α} {s : Set ι}

theorem antivaryOn_iff_forall_mul_nonpos :
    AntivaryOn f g s ↔ ∀ ⦃i⦄, i ∈ s → ∀ ⦃j⦄, j ∈ s → (f j - f i) * (g j - g i) ≤ 0 := by
  simp only [smul_eq_mul, antivaryOn_iff_forall_smul_nonpos]

