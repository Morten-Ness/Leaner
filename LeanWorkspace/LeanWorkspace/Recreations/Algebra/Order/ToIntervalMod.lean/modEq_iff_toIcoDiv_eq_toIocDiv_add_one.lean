import Mathlib

variable {α : Type*} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] [hα : Archimedean α]
  {p : α} (hp : 0 < p)
  {a b c : α} {n : ℤ}

theorem modEq_iff_toIcoDiv_eq_toIocDiv_add_one :
    a ≡ b [PMOD p] ↔ toIcoDiv hp a b = toIocDiv hp a b + 1 := by
  rw [AddCommGroup.modEq_iff_toIcoMod_add_period_eq_toIocMod hp, toIcoMod, toIocMod, ← eq_sub_iff_add_eq,
    sub_sub, sub_right_inj, ← add_one_zsmul, zsmul_left_inj hp]

