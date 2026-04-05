import Mathlib

variable {α : Type*} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] [hα : Archimedean α]
  {p : α} (hp : 0 < p)
  {a b c : α} {n : ℤ}

theorem toIocMod_periodic (a : α) : Function.Periodic (toIocMod hp a) p := toIocMod_add_right hp a

-- helper lemmas for when `a = 0`

