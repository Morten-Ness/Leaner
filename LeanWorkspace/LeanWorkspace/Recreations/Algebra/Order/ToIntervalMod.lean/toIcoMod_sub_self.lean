import Mathlib

variable {α : Type*} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] [hα : Archimedean α]
  {p : α} (hp : 0 < p)
  {a b c : α} {n : ℤ}

theorem toIcoMod_sub_self (a b : α) : toIcoMod hp a b - b = -toIcoDiv hp a b • p := by
  rw [toIcoMod, sub_sub_cancel_left, neg_smul]

