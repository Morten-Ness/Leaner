import Mathlib

variable {k E PE : Type*} [Field k] [AddCommGroup E] [Module k E] [AddTorsor E PE]

theorem slope_vadd_const (f : k → E) (c : PE) : (slope fun x => f x +ᵥ c) = slope f := by
  ext a b
  simp only [slope, vadd_vsub_vadd_cancel_right, vsub_eq_sub]

