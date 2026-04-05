import Mathlib

variable {α : Type*} {x y : α}

variable [PartialOrder α]

theorem IsSuccPrelimit.add_natCast_lt [AddMonoidWithOne α] [SuccAddOrder α]
    (hx : IsSuccPrelimit x) (hy : y < x) : ∀ n : ℕ, y + n < x
  | 0 => by simpa
  | n + 1 => by
    rw [Nat.cast_add_one, ← add_assoc]
    exact hx.add_one_lt (hx.add_natCast_lt hy n)
