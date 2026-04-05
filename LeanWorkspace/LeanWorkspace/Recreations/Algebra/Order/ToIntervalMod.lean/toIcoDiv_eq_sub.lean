import Mathlib

variable {α : Type*} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] [hα : Archimedean α]
  {p : α} (hp : 0 < p)
  {a b c : α} {n : ℤ}

theorem toIcoDiv_eq_sub (a b : α) : toIcoDiv hp a b = toIcoDiv hp 0 (b - a) := by
  rw [toIcoDiv_sub_eq_toIcoDiv_add, zero_add]

