import Mathlib

variable {α : Type u}

variable [Monoid α] [LinearOrder α] [CanonicallyOrderedMul α]

theorem bot_eq_one' [OrderBot α] : (⊥ : α) = 1 := bot_eq_one

