import Mathlib

variable {α : Type u}

variable {M : Type*} {N : Type*}

variable [Monoid M] {a b : M}

theorem val_inv_mul (h : IsUnit a) : ↑h.unit⁻¹ * a = 1 := Units.mul_inv _

