import Mathlib

variable {α : Type*} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] [hα : Archimedean α]
  {p : α} (hp : 0 < p)
  {a b c : α} {n : ℤ}

theorem toIcoDiv_nsmul_add (a b : α) (m : ℕ) : toIcoDiv hp a (m • p + b) = m + toIcoDiv hp a b := mod_cast toIcoDiv_zsmul_add hp a b m

