import Mathlib

variable {α : Type*} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] [hα : Archimedean α]
  {p : α} (hp : 0 < p)
  {a b c : α} {n : ℤ}

theorem toIocDiv_add_left' (a b : α) : toIocDiv hp (p + a) b = toIocDiv hp a b - 1 := by
  rw [add_comm, toIocDiv_add_right']

