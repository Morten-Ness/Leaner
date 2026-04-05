import Mathlib

variable {ι α β : Type*}

variable [Ring α] [LinearOrder α] [IsStrictOrderedRing α] {f g : ι → α} {s : Set ι}

theorem monovary_iff_mul_rearrangement :
    Monovary f g ↔ ∀ i j, f i * g j + f j * g i ≤ f i * g i + f j * g j := by
  simp only [smul_eq_mul, monovary_iff_smul_rearrangement]

