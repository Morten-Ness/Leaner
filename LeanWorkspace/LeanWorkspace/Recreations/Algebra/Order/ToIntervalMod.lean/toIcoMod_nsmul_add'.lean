import Mathlib

variable {α : Type*} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] [hα : Archimedean α]
  {p : α} (hp : 0 < p)
  {a b c : α} {n : ℤ}

theorem toIcoMod_nsmul_add' (a b : α) (m : ℕ) :
    toIcoMod hp (m • p + a) b = m • p + toIcoMod hp a b := mod_cast toIcoMod_zsmul_add' hp a b m

