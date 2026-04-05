import Mathlib

variable {α : Type u} {β : Type v} {R : Type x}

variable [Monoid α] [HasDistribNeg α]

theorem val_neg (u : αˣ) : (↑(-u) : α) = -u := rfl

