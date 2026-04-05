import Mathlib

variable (S : ShortComplex Ab.{u})

theorem ab_zero_apply (x : S.X₁) : S.g (S.f x) = 0 := by
  rw [← ConcreteCategory.comp_apply, S.zero]
  rfl

