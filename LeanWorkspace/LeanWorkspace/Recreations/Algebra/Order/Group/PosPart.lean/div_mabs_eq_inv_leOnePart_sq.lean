import Mathlib

variable {α : Type*}

variable [Lattice α]

variable [CommGroup α] [MulLeftMono α]

theorem div_mabs_eq_inv_leOnePart_sq (a : α) : a / |a|ₘ = (a⁻ᵐ ^ 2)⁻¹ := by
  rw [← mabs_div_eq_leOnePart_sq, inv_div]

