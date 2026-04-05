import Mathlib

variable {α : Type*} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] [hα : Archimedean α]
  {p : α} (hp : 0 < p)
  {a b c : α} {n : ℤ}

theorem toIocDiv_sub_nsmul' (a b : α) (m : ℕ) : toIocDiv hp (a - m • p) b = toIocDiv hp a b + m := mod_cast toIocDiv_sub_zsmul' hp a b m

