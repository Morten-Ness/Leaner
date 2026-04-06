import Mathlib

variable {α : Type u}

variable {M : Type*} {N : Type*}

variable [Monoid M] {a b : M}

theorem mul_val_inv (h : IsUnit a) : a * ↑h.unit⁻¹ = 1 := by
  simpa [h.unit_spec] using h.unit.mul_inv
