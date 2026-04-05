import Mathlib

variable {α : Type*} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] [hα : Archimedean α]
  {p : α} (hp : 0 < p)
  {a b c : α} {n : ℤ}

theorem toIocMod_nsmul_add' (a b : α) (m : ℕ) :
    toIocMod hp (m • p + a) b = m • p + toIocMod hp a b := mod_cast toIocMod_zsmul_add' hp a b m

