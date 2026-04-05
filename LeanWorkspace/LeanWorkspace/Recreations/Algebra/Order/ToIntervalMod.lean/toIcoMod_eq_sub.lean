import Mathlib

variable {α : Type*} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] [hα : Archimedean α]
  {p : α} (hp : 0 < p)
  {a b c : α} {n : ℤ}

theorem toIcoMod_eq_sub (a b : α) : toIcoMod hp a b = toIcoMod hp 0 (b - a) + a := by
  rw [toIcoMod_sub_eq_sub, zero_add, sub_add_cancel]

