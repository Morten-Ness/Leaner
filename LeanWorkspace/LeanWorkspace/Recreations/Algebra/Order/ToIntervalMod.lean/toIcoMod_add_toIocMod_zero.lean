import Mathlib

variable {α : Type*} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] [hα : Archimedean α]
  {p : α} (hp : 0 < p)
  {a b c : α} {n : ℤ}

theorem toIcoMod_add_toIocMod_zero (a b : α) :
    toIcoMod hp 0 (a - b) + toIocMod hp 0 (b - a) = p := by
  rw [toIcoMod_zero_sub_comm, sub_add_cancel]

