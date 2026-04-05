import Mathlib

variable {α : Type*} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] [hα : Archimedean α]
  {p : α} (hp : 0 < p)
  {a b c : α} {n : ℤ}

theorem toIcoMod_add_toIcoDiv_zsmul (a b : α) : toIcoMod hp a b + toIcoDiv hp a b • p = b := by
  rw [toIcoMod, sub_add_cancel]

