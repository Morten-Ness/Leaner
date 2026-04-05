import Mathlib

variable {α : Type*} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] [hα : Archimedean α]
  {p : α} (hp : 0 < p)
  {a b c : α} {n : ℤ}

theorem toIocDiv_zsmul_sub_toIocMod (a b : α) : toIocDiv hp a b • p + toIocMod hp a b = b := by
  rw [add_comm, toIocMod_add_toIocDiv_zsmul]

