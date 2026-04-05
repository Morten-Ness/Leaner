import Mathlib

variable {α : Type*} {x y : α}

variable [PartialOrder α]

theorem succ_eq_zero [AddZeroClass α] [OrderBot α] [CanonicallyOrderedAdd α] [One α] [NoMaxOrder α]
    [SuccAddOrder α] {a : WithBot α} : WithBot.succ a = 0 ↔ a = ⊥ := by
  cases a
  · simp [bot_eq_zero]
  · rename_i a
    simp only [WithBot.succ_coe, WithBot.coe_ne_bot, iff_false, Order.succ_eq_add_one]
    by_contra h
    simpa [h] using max_of_succ_le (a := a)

