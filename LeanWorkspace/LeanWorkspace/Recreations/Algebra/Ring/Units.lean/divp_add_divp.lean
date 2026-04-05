import Mathlib

variable {α : Type u} {β : Type v} {R : Type x}

theorem divp_add_divp [CommSemiring α] (a b : α) (u₁ u₂ : αˣ) :
    a /ₚ u₁ + b /ₚ u₂ = (a * u₂ + u₁ * b) /ₚ (u₁ * u₂) := by
  simp only [divp, add_mul, mul_inv_rev, val_mul]
  rw [mul_comm (↑u₁ * b), mul_comm b]
  rw [← mul_assoc, ← mul_assoc, mul_assoc a, mul_assoc (↑u₂⁻¹ : α), mul_inv, inv_mul, mul_one,
    mul_one]
  -- Porting note: `assoc_rw` not ported: `assoc_rw [mul_inv, mul_inv, mul_one, mul_one]`

