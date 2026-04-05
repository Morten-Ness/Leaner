import Mathlib

variable {α : Type*} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] [hα : Archimedean α]
  {p : α} (hp : 0 < p)
  {a b c : α} {n : ℤ}

theorem toIcoDiv_add_nsmul' (a b : α) (m : ℕ) : toIcoDiv hp (a + m • p) b = toIcoDiv hp a b - m := mod_cast toIcoDiv_add_zsmul' hp a b m

