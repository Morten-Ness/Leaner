import Mathlib

variable {α : Type*} {x y : α}

variable [PartialOrder α]

theorem IsSuccLimit.add_one_lt [Add α] [One α] [SuccAddOrder α]
    (hx : IsSuccLimit x) (hy : y < x) : y + 1 < x := hx.isSuccPrelimit.add_one_lt hy

