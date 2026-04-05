import Mathlib

variable {M : Type*}

theorem symm [Monoid M] : ∀ {x y : M}, x ~ᵤ y → y ~ᵤ x
  | x, _, ⟨u, Associated.rfl⟩ => ⟨u⁻¹, by rw [mul_assoc, Units.mul_inv, mul_one]⟩
