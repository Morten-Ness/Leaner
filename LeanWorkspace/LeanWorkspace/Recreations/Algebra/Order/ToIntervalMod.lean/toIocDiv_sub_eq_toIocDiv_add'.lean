import Mathlib

variable {α : Type*} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] [hα : Archimedean α]
  {p : α} (hp : 0 < p)
  {a b c : α} {n : ℤ}

theorem toIocDiv_sub_eq_toIocDiv_add' (a b c : α) :
    toIocDiv hp (a - c) b = toIocDiv hp a (b + c) := by
  rw [← sub_neg_eq_add, toIocDiv_sub_eq_toIocDiv_add, sub_eq_add_neg]

