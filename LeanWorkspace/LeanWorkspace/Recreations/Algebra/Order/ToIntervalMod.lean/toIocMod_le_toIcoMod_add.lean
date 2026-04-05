import Mathlib

variable {α : Type*} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] [hα : Archimedean α]
  {p : α} (hp : 0 < p)
  {a b c : α} {n : ℤ}

theorem toIocMod_le_toIcoMod_add (a b : α) : toIocMod hp a b ≤ toIcoMod hp a b + p := by
  rw [toIcoMod, toIocMod, sub_add, sub_le_sub_iff_left, sub_le_iff_le_add, ← add_one_zsmul,
    (zsmul_left_strictMono hp).le_iff_le]
  apply (toIocDiv_wcovBy_toIcoDiv _ _ _).le_succ

