import Mathlib

variable {ι α β : Type*}

variable [Ring α] [LinearOrder α] [IsStrictOrderedRing α] {f g : ι → α} {s : Set ι}

theorem monovary_iff_forall_mul_nonneg : Monovary f g ↔ ∀ i j, 0 ≤ (f j - f i) * (g j - g i) := by
  simp only [smul_eq_mul, monovary_iff_forall_smul_nonneg]

