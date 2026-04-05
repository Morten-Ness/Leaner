import Mathlib

variable {α : Type*} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] [hα : Archimedean α]
  {p : α} (hp : 0 < p)
  {a b c : α} {n : ℤ}

theorem modEq_iff_toIcoMod_eq_left : a ≡ b [PMOD p] ↔ toIcoMod hp a b = a := modEq_iff_eq_add_zsmul.trans
    ⟨by
      rintro ⟨n, rfl⟩
      rw [toIcoMod_add_zsmul, toIcoMod_apply_left], fun h => ⟨toIcoDiv hp a b, eq_add_of_sub_eq h⟩⟩

