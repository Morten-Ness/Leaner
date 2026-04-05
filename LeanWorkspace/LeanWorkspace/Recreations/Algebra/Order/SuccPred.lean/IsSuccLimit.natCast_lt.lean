import Mathlib

variable {α : Type*} {x y : α}

variable [PartialOrder α]

theorem IsSuccLimit.natCast_lt [AddMonoidWithOne α] [SuccAddOrder α]
    [OrderBot α] [CanonicallyOrderedAdd α]
    (hx : IsSuccLimit x) : ∀ n : ℕ, n < x := by
  simpa [bot_eq_zero] using hx.add_natCast_lt hx.bot_lt

