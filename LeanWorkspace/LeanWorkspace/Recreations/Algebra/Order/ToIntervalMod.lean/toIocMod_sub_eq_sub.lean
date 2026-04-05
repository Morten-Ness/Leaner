import Mathlib

variable {α : Type*} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] [hα : Archimedean α]
  {p : α} (hp : 0 < p)
  {a b c : α} {n : ℤ}

theorem toIocMod_sub_eq_sub (a b c : α) : toIocMod hp a (b - c) = toIocMod hp (a + c) b - c := by
  simp_rw [toIocMod, toIocDiv_sub_eq_toIocDiv_add, sub_right_comm]

