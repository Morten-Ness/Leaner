import Mathlib

variable {ι α β : Type*}

variable [Ring α] [LinearOrder α] [IsStrictOrderedRing α] {f g : ι → α} {s : Set ι}

theorem antivary_iff_forall_mul_nonpos : Antivary f g ↔ ∀ i j, (f j - f i) * (g j - g i) ≤ 0 := by
  simp only [smul_eq_mul, antivary_iff_forall_smul_nonpos]

