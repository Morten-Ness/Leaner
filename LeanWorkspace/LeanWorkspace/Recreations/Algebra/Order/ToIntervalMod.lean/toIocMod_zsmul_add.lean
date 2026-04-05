import Mathlib

variable {α : Type*} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] [hα : Archimedean α]
  {p : α} (hp : 0 < p)
  {a b c : α} {n : ℤ}

theorem toIocMod_zsmul_add (a b : α) (m : ℤ) : toIocMod hp a (m • p + b) = toIocMod hp a b := by
  rw [add_comm, toIocMod_add_zsmul]

