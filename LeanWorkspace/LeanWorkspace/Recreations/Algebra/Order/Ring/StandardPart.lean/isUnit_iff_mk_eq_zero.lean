import Mathlib

theorem isUnit_iff_mk_eq_zero {x : ArchimedeanClass.FiniteElement K} : IsUnit x ↔ ArchimedeanClass.FiniteElement.mk x.1 = 0 := by
  rw [← not_iff_not, ArchimedeanClass.FiniteElement.not_isUnit_iff_mk_pos, lt_iff_not_ge, x.2.ge_iff_eq']

