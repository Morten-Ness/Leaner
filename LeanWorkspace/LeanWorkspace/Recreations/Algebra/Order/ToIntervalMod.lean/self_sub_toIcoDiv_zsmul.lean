import Mathlib

variable {α : Type*} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] [hα : Archimedean α]
  {p : α} (hp : 0 < p)
  {a b c : α} {n : ℤ}

theorem self_sub_toIcoDiv_zsmul (a b : α) : b - toIcoDiv hp a b • p = toIcoMod hp a b := rfl

