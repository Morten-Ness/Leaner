import Mathlib

variable {α : Type u}

variable [MulOneClass α]

variable [PartialOrder α] [CanonicallyOrderedMul α] {a b c : α}

theorem bot_eq_one [OrderBot α] : (⊥ : α) = 1 := isBot_one.eq_bot.symm

