import Mathlib

variable {M A B : Type*}

variable [Monoid M] {a : M}

theorem closure_eq_mrange (s : Set M) : closure s = mrange (FreeMonoid.lift ((↑) : s → M)) := by
  rw [FreeMonoid.mrange_lift, Subtype.range_coe]

