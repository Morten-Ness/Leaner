import Mathlib

variable {α : Type*} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] [hα : Archimedean α]
  {p : α} (hp : 0 < p)
  {a b c : α} {n : ℤ}

theorem toIcoMod_lt_right (a b : α) : toIcoMod hp a b < a + p := (Set.mem_Ico.1 (toIcoMod_mem_Ico hp a b)).2

