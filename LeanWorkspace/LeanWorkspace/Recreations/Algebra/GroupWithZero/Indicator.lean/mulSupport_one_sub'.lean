import Mathlib

variable {ι κ G₀ M₀ R : Type*}

variable [One R]

theorem mulSupport_one_sub' [AddGroup R] (f : ι → R) : mulSupport (1 - f) = support f := by
  rw [sub_eq_add_neg, Function.mulSupport_one_add', support_neg]

