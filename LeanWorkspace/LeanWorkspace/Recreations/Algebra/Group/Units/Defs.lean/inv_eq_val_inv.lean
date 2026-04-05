import Mathlib

variable {α : Type u}

variable [Monoid α]

variable (a b : αˣ) {u : αˣ}

theorem inv_eq_val_inv : a.inv = ((a⁻¹ : αˣ) : α) := rfl

