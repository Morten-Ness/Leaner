import Mathlib

variable {α : Type*} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] [hα : Archimedean α]
  {p : α} (hp : 0 < p)
  {a b c : α} {n : ℤ}

theorem left_le_toIcoMod (a b : α) : a ≤ toIcoMod hp a b := (Set.mem_Ico.1 (toIcoMod_mem_Ico hp a b)).1

