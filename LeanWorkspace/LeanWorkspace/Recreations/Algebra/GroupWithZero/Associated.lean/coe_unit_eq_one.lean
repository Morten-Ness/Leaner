import Mathlib

variable {M : Type*}

variable [CommMonoid M]

theorem coe_unit_eq_one (u : (Associates M)ˣ) : (u : Associates M) = 1 := by
  simp [eq_iff_true_of_subsingleton]

