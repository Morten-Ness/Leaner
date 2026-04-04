import Mathlib

variable {k E PE : Type*} [Field k] [AddCommGroup E] [Module k E] [AddTorsor E PE]

theorem slope_def_field (f : k → k) (a b : k) : slope f a b = (f b - f a) / (b - a) := (div_eq_inv_mul _ _).symm

