import Mathlib

variable {α : Type*} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] [hα : Archimedean α]
  {p : α} (hp : 0 < p)
  {a b c : α} {n : ℤ}

theorem toIcoMod_add_right_eq_add (a b c : α) :
    toIcoMod hp a (b + c) = toIcoMod hp (a - c) b + c := by
  simp_rw [toIcoMod, toIcoDiv_sub_eq_toIcoDiv_add', sub_add_eq_add_sub]

