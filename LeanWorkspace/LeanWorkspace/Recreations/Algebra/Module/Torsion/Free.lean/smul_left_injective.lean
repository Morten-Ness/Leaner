import Mathlib

variable {R S M N : Type*}

variable [Ring R] [AddCommGroup M] [Module R M] {m : M} {r₁ r₂ : R}

variable [IsCancelMulZero R] [IsTorsionFree R M]

theorem smul_left_injective (hm : m ≠ 0) : ((· • m) : R → M).Injective := by
  rintro r₁ r₂ hr
  dsimp at hr
  rwa [← sub_eq_zero, ← sub_smul, smul_eq_zero_iff_left hm, sub_eq_zero] at hr

