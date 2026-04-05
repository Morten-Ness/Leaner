import Mathlib

variable {α : Type u}

variable [Monoid α]

variable (a b : αˣ) {u : αˣ}

theorem val_mul : (↑(a * b) : α) = a * b := rfl

