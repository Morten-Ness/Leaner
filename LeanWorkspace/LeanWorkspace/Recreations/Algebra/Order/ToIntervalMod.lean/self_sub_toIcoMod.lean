import Mathlib

variable {α : Type*} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] [hα : Archimedean α]
  {p : α} (hp : 0 < p)
  {a b c : α} {n : ℤ}

theorem self_sub_toIcoMod (a b : α) : b - toIcoMod hp a b = toIcoDiv hp a b • p := by
  rw [toIcoMod, sub_sub_cancel]

