import Mathlib

variable {α : Type*} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] [hα : Archimedean α]
  {p : α} (hp : 0 < p)
  {a b c : α} {n : ℤ}

theorem toIcoMod_sub_nsmul' (a b : α) (m : ℕ) :
    toIcoMod hp (a - m • p) b = toIcoMod hp a b - m • p := mod_cast toIcoMod_sub_zsmul' hp a b m

