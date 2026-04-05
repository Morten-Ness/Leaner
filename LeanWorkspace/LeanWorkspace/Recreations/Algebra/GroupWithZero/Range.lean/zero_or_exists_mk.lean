import Mathlib

variable [GroupWithZero A] [GroupWithZero B] [MonoidWithZeroHomClass F A B] {f}

variable [MonoidWithZero A] [CommGroupWithZero B] [MonoidWithZeroHomClass F A B]

theorem zero_or_exists_mk (x : ValueGroup₀ f) :
    x = 0 ∨ ∃ r s hr hs, x = MonoidWithZeroHom.valueGroup.mk f r s hr hs := by
  obtain _ | ⟨x, hx⟩ := x
  · left; rfl
  · rw [mem_valueGroup_iff_of_comm'] at hx
    obtain ⟨r, hr, s, hs, hrs⟩ := hx
    refine .inr ⟨r, s, hr, hs, Option.some_inj.mpr <| by
      simp only [MonoidWithZeroHom.valueGroup.mk, Subtype.mk.injEq]
      rw [eq_inv_mul_iff_mul_eq]
      simp [← hrs, mul_comm]⟩

