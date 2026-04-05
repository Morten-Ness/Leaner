import Mathlib

variable {α : Type u} {β : Type v} {R : Type x}

variable [Monoid α] [HasDistribNeg α]

theorem coe_neg_one : ((-1 : αˣ) : α) = -1 := rfl

