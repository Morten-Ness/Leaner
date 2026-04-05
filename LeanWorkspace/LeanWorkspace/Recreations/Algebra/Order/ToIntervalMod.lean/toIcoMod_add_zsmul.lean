import Mathlib

variable {α : Type*} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] [hα : Archimedean α]
  {p : α} (hp : 0 < p)
  {a b c : α} {n : ℤ}

theorem toIcoMod_add_zsmul (a b : α) (m : ℤ) : toIcoMod hp a (b + m • p) = toIcoMod hp a b := by
  rw [toIcoMod, toIcoDiv_add_zsmul, toIcoMod, add_smul]
  abel

