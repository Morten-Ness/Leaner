import Mathlib

variable {α : Type*} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] [hα : Archimedean α]
  {p : α} (hp : 0 < p)
  {a b c : α} {n : ℤ}

theorem toIocDiv_neg (a b : α) : toIocDiv hp a (-b) = -(toIcoDiv hp (-a) b + 1) := by
  rw [← neg_neg b, toIcoDiv_neg, neg_neg, neg_neg, neg_add', neg_neg, add_sub_cancel_right]

