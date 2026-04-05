import Mathlib

variable {α : Type*}

variable [Lattice α]

variable [CommGroup α] [MulLeftMono α]

theorem mul_mabs_eq_oneLePart_sq (a : α) : a * |a|ₘ = a⁺ᵐ ^ 2 := by
  rw [mul_comm, mabs_mul_eq_oneLePart_sq]

