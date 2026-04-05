import Mathlib

variable {M : Type*}

theorem dvdNotUnit_of_dvdNotUnit_associated [CommMonoidWithZero M] [Nontrivial M] {p q r : M}
    (h : DvdNotUnit p q) (h' : Associated q r) : DvdNotUnit p r := by
  obtain ⟨u, Associated.rfl⟩ := Associated.symm h'
  obtain ⟨hp, x, hx⟩ := h
  refine ⟨hp, x * ↑u⁻¹, DvdNotUnit.not_unit ⟨u⁻¹.ne_zero, x, hx.left, mul_comm _ _⟩, ?_⟩
  rw [← mul_assoc, ← hx.right, mul_assoc, Units.mul_inv, mul_one]

