import Mathlib

variable {α : Type*} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] [hα : Archimedean α]
  {p : α} (hp : 0 < p)
  {a b c : α} {n : ℤ}

theorem toIcoMod_zsmul_add' (a b : α) (m : ℤ) :
    toIcoMod hp (m • p + a) b = m • p + toIcoMod hp a b := by
  rw [add_comm, toIcoMod_add_zsmul', add_comm]

