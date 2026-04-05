import Mathlib

variable {α : Type*} {x y : α}

variable [PartialOrder α]

theorem IsSuccLimit.add_natCast_lt [AddMonoidWithOne α] [SuccAddOrder α]
    (hx : IsSuccLimit x) (hy : y < x) : ∀ n : ℕ, y + n < x := hx.isSuccPrelimit.add_natCast_lt hy

