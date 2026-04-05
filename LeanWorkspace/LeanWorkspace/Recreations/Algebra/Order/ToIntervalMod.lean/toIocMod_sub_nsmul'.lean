import Mathlib

variable {α : Type*} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] [hα : Archimedean α]
  {p : α} (hp : 0 < p)
  {a b c : α} {n : ℤ}

theorem toIocMod_sub_nsmul' (a b : α) (m : ℕ) :
    toIocMod hp (a - m • p) b = toIocMod hp a b - m • p := mod_cast toIocMod_sub_zsmul' hp a b m

