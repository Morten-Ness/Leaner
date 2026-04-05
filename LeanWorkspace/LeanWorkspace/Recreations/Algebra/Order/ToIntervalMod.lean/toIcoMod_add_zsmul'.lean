import Mathlib

variable {α : Type*} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] [hα : Archimedean α]
  {p : α} (hp : 0 < p)
  {a b c : α} {n : ℤ}

theorem toIcoMod_add_zsmul' (a b : α) (m : ℤ) :
    toIcoMod hp (a + m • p) b = toIcoMod hp a b + m • p := by
  simp only [toIcoMod, toIcoDiv_add_zsmul', sub_smul, sub_add]

