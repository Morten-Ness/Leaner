import Mathlib

variable {α : Type*} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] [hα : Archimedean α]
  {p : α} (hp : 0 < p)
  {a b c : α} {n : ℤ}

theorem toIocMod_eq_sub (a b : α) : toIocMod hp a b = toIocMod hp 0 (b - a) + a := by
  rw [toIocMod_sub_eq_sub, zero_add, sub_add_cancel]

