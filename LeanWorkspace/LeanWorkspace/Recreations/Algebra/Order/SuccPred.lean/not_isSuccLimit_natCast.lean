import Mathlib

variable {α : Type*} {x y : α}

variable [PartialOrder α]

theorem not_isSuccLimit_natCast [AddMonoidWithOne α] [SuccAddOrder α]
    [OrderBot α] [CanonicallyOrderedAdd α]
    (n : ℕ) : ¬ IsSuccLimit (n : α) := fun h ↦ (h.natCast_lt n).false

