import Mathlib

variable {α : Type u}

variable [Monoid α]

variable (a b : αˣ) {u : αˣ}

theorem val_pow_eq_pow_val (n : ℕ) : ↑(a ^ n) = (a ^ n : α) := rfl

