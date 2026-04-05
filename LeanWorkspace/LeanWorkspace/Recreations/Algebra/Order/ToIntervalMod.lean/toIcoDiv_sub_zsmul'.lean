import Mathlib

variable {α : Type*} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] [hα : Archimedean α]
  {p : α} (hp : 0 < p)
  {a b c : α} {n : ℤ}

theorem toIcoDiv_sub_zsmul' (a b : α) (m : ℤ) :
    toIcoDiv hp (a - m • p) b = toIcoDiv hp a b + m := by
  rw [sub_eq_add_neg, ← neg_smul, toIcoDiv_add_zsmul', sub_neg_eq_add]

