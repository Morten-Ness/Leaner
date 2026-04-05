import Mathlib

variable {α : Type*} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] [hα : Archimedean α]
  {p : α} (hp : 0 < p)
  {a b c : α} {n : ℤ}

theorem toIocDiv_eq_sub (a b : α) : toIocDiv hp a b = toIocDiv hp 0 (b - a) := by
  rw [toIocDiv_sub_eq_toIocDiv_add, zero_add]

