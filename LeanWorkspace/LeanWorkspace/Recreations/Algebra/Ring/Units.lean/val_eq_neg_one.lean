import Mathlib

variable {α : Type u} {β : Type v} {R : Type x}

variable [Monoid α] [HasDistribNeg α]

theorem val_eq_neg_one {a : αˣ} : (a : α) = -1 ↔ a = -1 := by
  rw [← Units.coe_neg_one, val_inj]

