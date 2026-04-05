import Mathlib

variable {α : Type*} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] [hα : Archimedean α]
  {p : α} (hp : 0 < p)
  {a b c : α} {n : ℤ}

theorem toIocMod_le_right (a b : α) : toIocMod hp a b ≤ a + p := (Set.mem_Ioc.1 (toIocMod_mem_Ioc hp a b)).2

