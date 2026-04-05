import Mathlib

variable {α : Type u}

variable [Monoid α]

variable (a b : αˣ) {u : αˣ}

theorem inv_pow_eq_pow_inv (n : ℕ) : ↑(a ^ n)⁻¹ = (a⁻¹ ^ n : α) := rfl

