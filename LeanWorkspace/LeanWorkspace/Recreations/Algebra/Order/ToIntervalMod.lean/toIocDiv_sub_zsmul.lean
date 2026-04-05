import Mathlib

variable {α : Type*} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] [hα : Archimedean α]
  {p : α} (hp : 0 < p)
  {a b c : α} {n : ℤ}

theorem toIocDiv_sub_zsmul (a b : α) (m : ℤ) : toIocDiv hp a (b - m • p) = toIocDiv hp a b - m := by
  rw [sub_eq_add_neg, ← neg_smul, toIocDiv_add_zsmul, sub_eq_add_neg]

