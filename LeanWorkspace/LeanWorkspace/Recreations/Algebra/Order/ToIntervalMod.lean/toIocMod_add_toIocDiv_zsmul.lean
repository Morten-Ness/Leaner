import Mathlib

variable {α : Type*} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] [hα : Archimedean α]
  {p : α} (hp : 0 < p)
  {a b c : α} {n : ℤ}

theorem toIocMod_add_toIocDiv_zsmul (a b : α) : toIocMod hp a b + toIocDiv hp a b • p = b := by
  rw [toIocMod, sub_add_cancel]

