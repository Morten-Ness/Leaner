import Mathlib

variable {α : Type*} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] [hα : Archimedean α]
  {p : α} (hp : 0 < p)
  {a b c : α} {n : ℤ}

theorem toIocMod_zero_sub_comm (a b : α) : toIocMod hp 0 (a - b) = p - toIcoMod hp 0 (b - a) := by
  rw [← neg_sub, toIocMod_neg, neg_zero]

