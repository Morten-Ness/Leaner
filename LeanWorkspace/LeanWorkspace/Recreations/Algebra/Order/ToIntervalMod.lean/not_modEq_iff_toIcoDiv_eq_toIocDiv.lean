import Mathlib

variable {α : Type*} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] [hα : Archimedean α]
  {p : α} (hp : 0 < p)
  {a b c : α} {n : ℤ}

theorem not_modEq_iff_toIcoDiv_eq_toIocDiv :
    ¬a ≡ b [PMOD p] ↔ toIcoDiv hp a b = toIocDiv hp a b := by
  rw [AddCommGroup.not_modEq_iff_toIcoMod_eq_toIocMod hp, toIcoMod, toIocMod, sub_right_inj,
    zsmul_left_inj hp]

