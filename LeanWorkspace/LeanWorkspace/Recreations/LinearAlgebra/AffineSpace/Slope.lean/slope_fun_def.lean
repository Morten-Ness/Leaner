import Mathlib

variable {k E PE : Type*} [Field k] [AddCommGroup E] [Module k E] [AddTorsor E PE]

theorem slope_fun_def (f : k → PE) : slope f = fun a b => (b - a)⁻¹ • (f b -ᵥ f a) := rfl

