import Mathlib

variable {α R M M₂ : Type*}

variable [MulZeroOneClass R]

theorem smul_indicator_one_apply (s : Set α) (r : R) (a : α) :
    r • s.indicator (1 : α → R) a = s.indicator (fun _ ↦ r) a := by
  simp_rw [← Set.indicator_const_smul_apply, Pi.one_apply, smul_eq_mul, mul_one]

