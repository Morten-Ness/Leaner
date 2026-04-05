import Mathlib

variable {α : Type*} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] [hα : Archimedean α]
  {p : α} (hp : 0 < p)
  {a b c : α} {n : ℤ}

theorem toIcoMod_le_toIocMod (a b : α) : toIcoMod hp a b ≤ toIocMod hp a b := by
  rw [toIcoMod, toIocMod, sub_le_sub_iff_left]
  exact zsmul_left_mono hp.le (toIocDiv_wcovBy_toIcoDiv _ _ _).le

