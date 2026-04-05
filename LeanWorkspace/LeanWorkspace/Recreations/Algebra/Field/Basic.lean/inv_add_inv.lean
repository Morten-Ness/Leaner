import Mathlib

variable {K L : Type*}

variable [Semifield K] {a b d : K}

theorem inv_add_inv (ha : a ≠ 0) (hb : b ≠ 0) : a⁻¹ + b⁻¹ = (a + b) / (a * b) := (Commute.all a _).inv_add_inv ha hb

