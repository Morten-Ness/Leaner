import Mathlib

variable {α : Type u}

variable {M : Type*} {N : Type*}

variable [Monoid M] {a b : M}

theorem mul_val_inv (h : IsUnit a) : a * ↑h.unit⁻¹ = 1 := by
  rw [← Units.mul_inv h.unit]; congr

