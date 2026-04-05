import Mathlib

variable {α : Type*}

variable [Lattice α]

variable [Group α] {a b : α}

variable [MulLeftMono α]

variable [MulRightMono α]

theorem leOnePart_eq_inv_inf_one (a : α) : a⁻ᵐ = (a ⊓ 1)⁻¹ := by
  rw [leOnePart_def, ← inv_inj, inv_sup, inv_inv, inv_inv, inv_one]

-- Bourbaki A.VI.12 Prop 9 d)

