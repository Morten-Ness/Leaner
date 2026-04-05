import Mathlib

variable {α : Type*} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] [hα : Archimedean α]
  {p : α} (hp : 0 < p)
  {a b c : α} {n : ℤ}

theorem toIocMod_sub (a b : α) : toIocMod hp a (b - p) = toIocMod hp a b := by
  simpa only [one_zsmul] using toIocMod_sub_zsmul hp a b 1

