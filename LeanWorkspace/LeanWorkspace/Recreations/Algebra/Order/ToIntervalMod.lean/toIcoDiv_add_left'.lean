import Mathlib

variable {α : Type*} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] [hα : Archimedean α]
  {p : α} (hp : 0 < p)
  {a b c : α} {n : ℤ}

theorem toIcoDiv_add_left' (a b : α) : toIcoDiv hp (p + a) b = toIcoDiv hp a b - 1 := by
  rw [add_comm, toIcoDiv_add_right']

