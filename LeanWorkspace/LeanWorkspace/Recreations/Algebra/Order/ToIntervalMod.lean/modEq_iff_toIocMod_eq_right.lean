import Mathlib

variable {α : Type*} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] [hα : Archimedean α]
  {p : α} (hp : 0 < p)
  {a b c : α} {n : ℤ}

theorem modEq_iff_toIocMod_eq_right : a ≡ b [PMOD p] ↔ toIocMod hp a b = a + p := by
  refine modEq_iff_eq_add_zsmul.trans ⟨?_, fun h => ⟨toIocDiv hp a b + 1, ?_⟩⟩
  · rintro ⟨z, rfl⟩
    rw [toIocMod_add_zsmul, toIocMod_apply_left]
  · rwa [add_one_zsmul, add_left_comm, ← sub_eq_iff_eq_add']

alias ⟨ModEq.toIcoMod_eq_left, _⟩ := AddCommGroup.modEq_iff_toIcoMod_eq_left

alias ⟨ModEq.toIcoMod_eq_right, _⟩ := modEq_iff_toIocMod_eq_right

