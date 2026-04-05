import Mathlib

variable {α : Type*} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] [hα : Archimedean α]
  {p : α} (hp : 0 < p)
  {a b c : α} {n : ℤ}

theorem toIocMod_sub_self (a b : α) : toIocMod hp a b - b = -toIocDiv hp a b • p := by
  rw [toIocMod, sub_sub_cancel_left, neg_smul]

