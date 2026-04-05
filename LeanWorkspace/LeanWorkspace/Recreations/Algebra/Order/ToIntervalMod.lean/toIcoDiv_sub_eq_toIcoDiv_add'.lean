import Mathlib

variable {α : Type*} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] [hα : Archimedean α]
  {p : α} (hp : 0 < p)
  {a b c : α} {n : ℤ}

theorem toIcoDiv_sub_eq_toIcoDiv_add' (a b c : α) :
    toIcoDiv hp (a - c) b = toIcoDiv hp a (b + c) := by
  rw [← sub_neg_eq_add, toIcoDiv_sub_eq_toIcoDiv_add, sub_eq_add_neg]

