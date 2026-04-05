import Mathlib

variable {α : Type*} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] [hα : Archimedean α]
  {p : α} (hp : 0 < p)
  {a b c : α} {n : ℤ}

theorem toIocDiv_nsmul_add (a b : α) (m : ℕ) : toIocDiv hp a (m • p + b) = m + toIocDiv hp a b := mod_cast toIocDiv_zsmul_add hp a b m

