import Mathlib

variable {α : Type*} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] [hα : Archimedean α]
  {p : α} (hp : 0 < p)
  {a b c : α} {n : ℤ}

theorem toIcoDiv_zsmul_add (a b : α) (m : ℤ) : toIcoDiv hp a (m • p + b) = m + toIcoDiv hp a b := by
  rw [add_comm, toIcoDiv_add_zsmul, add_comm]

