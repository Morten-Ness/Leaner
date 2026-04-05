import Mathlib

variable {α : Type*} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] [hα : Archimedean α]
  {p : α} (hp : 0 < p)
  {a b c : α} {n : ℤ}

theorem toIcoMod_sub (a b : α) : toIcoMod hp a (b - p) = toIcoMod hp a b := by
  simpa only [one_zsmul] using toIcoMod_sub_zsmul hp a b 1

