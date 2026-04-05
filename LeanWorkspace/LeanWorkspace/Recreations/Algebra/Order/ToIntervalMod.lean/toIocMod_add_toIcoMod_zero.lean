import Mathlib

variable {α : Type*} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] [hα : Archimedean α]
  {p : α} (hp : 0 < p)
  {a b c : α} {n : ℤ}

theorem toIocMod_add_toIcoMod_zero (a b : α) :
    toIocMod hp 0 (a - b) + toIcoMod hp 0 (b - a) = p := by
  rw [_root_.add_comm, toIcoMod_add_toIocMod_zero]

