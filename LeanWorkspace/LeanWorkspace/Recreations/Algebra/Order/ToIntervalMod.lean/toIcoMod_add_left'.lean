import Mathlib

variable {α : Type*} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] [hα : Archimedean α]
  {p : α} (hp : 0 < p)
  {a b c : α} {n : ℤ}

theorem toIcoMod_add_left' (a b : α) : toIcoMod hp (p + a) b = p + toIcoMod hp a b := by
  rw [add_comm, toIcoMod_add_right', add_comm]

