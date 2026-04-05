import Mathlib

variable {M : Type*}

theorem unit_associated_one [Monoid M] {u : Mˣ} : (u : M) ~ᵤ 1 := ⟨u⁻¹, Units.mul_inv u⟩

