import Mathlib

variable {α : Type*} {x y : α}

variable [PartialOrder α]

theorem IsPredPrelimit.lt_sub_natCast [AddCommGroupWithOne α] [PredSubOrder α]
    (hx : IsPredPrelimit x) (hy : x < y) : ∀ n : ℕ, x < y - n
  | 0 => by simpa
  | n + 1 => by
    rw [Nat.cast_add_one, ← sub_sub]
    exact hx.lt_sub_one (hx.lt_sub_natCast hy n)
