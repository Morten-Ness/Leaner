import Mathlib

variable {α : Type*} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] [hα : Archimedean α]
  {p : α} (hp : 0 < p)
  {a b c : α} {n : ℤ}

theorem toIcoMod_sub_zsmul' (a b : α) (m : ℤ) :
    toIcoMod hp (a - m • p) b = toIcoMod hp a b - m • p := by
  simp_rw [sub_eq_add_neg, ← neg_smul, toIcoMod_add_zsmul']

