import Mathlib

variable {α : Type u}

variable [Monoid α]

theorem val_inj {a b : αˣ} : (a : α) = b ↔ a = b := Units.val_injective.eq_iff

