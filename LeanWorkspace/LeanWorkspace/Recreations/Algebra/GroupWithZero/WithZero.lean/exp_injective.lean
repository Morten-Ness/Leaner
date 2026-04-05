import Mathlib

variable {α β γ : Type*}

variable {M G : Type*}

theorem exp_injective : Function.Injective (WithZero.exp : M → Mᵐ⁰) := Multiplicative.ofAdd.injective.comp WithZero.coe_injective

