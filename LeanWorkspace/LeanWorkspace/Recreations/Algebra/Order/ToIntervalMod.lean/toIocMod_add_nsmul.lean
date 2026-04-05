import Mathlib

variable {α : Type*} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] [hα : Archimedean α]
  {p : α} (hp : 0 < p)
  {a b c : α} {n : ℤ}

theorem toIocMod_add_nsmul (a b : α) (m : ℕ) : toIocMod hp a (b + m • p) = toIocMod hp a b := mod_cast toIocMod_add_zsmul hp a b m

