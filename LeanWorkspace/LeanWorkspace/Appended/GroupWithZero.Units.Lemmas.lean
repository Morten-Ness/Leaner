import Mathlib

section

open scoped Ring

variable {M M₀ G₀ M₀' G₀' F F' : Type*}

variable [MonoidWithZero M₀]

variable [GroupWithZero G₀] [Nontrivial M₀] [MonoidWithZero M₀'] [FunLike F G₀ M₀]
  [MonoidWithZeroHomClass F G₀ M₀] [FunLike F' G₀ M₀']
  (f : F) {a : G₀}

theorem eq_on_inv₀ [MonoidWithZeroHomClass F' G₀ M₀'] (f g : F') (h : f a = g a) :
    f a⁻¹ = g a⁻¹ := by
  rcases eq_or_ne a 0 with (rfl | ha)
  · rw [inv_zero, map_zero, map_zero]
  · exact (IsUnit.mk0 a ha).eq_on_inv f g h

end

section

open scoped Ring

variable {M M₀ G₀ M₀' G₀' F F' : Type*}

variable [MonoidWithZero M₀]

variable [Monoid M] [GroupWithZero G₀]

theorem isLocalHom_of_exists_map_ne_one [FunLike F G₀ M] [MonoidHomClass F G₀ M] {f : F}
    (hf : ∃ x : G₀, f x ≠ 1) : IsLocalHom f where
  map_nonunit a h := by
    rcases eq_or_ne a 0 with (rfl | h)
    · obtain ⟨t, ht⟩ := hf
      refine (ht ?_).elim
      have := map_mul f t 0
      rw [← one_mul (f (t * 0)), mul_zero] at this
      exact (h.mul_right_cancel this).symm
    · exact ⟨⟨a, a⁻¹, mul_inv_cancel₀ h, inv_mul_cancel₀ h⟩, rfl⟩

end

section

open scoped Ring

variable {M M₀ G₀ M₀' G₀' F F' : Type*}

variable [MonoidWithZero M₀]

variable [GroupWithZero G₀] [GroupWithZero G₀'] [FunLike F G₀ G₀']
  [MonoidWithZeroHomClass F G₀ G₀'] (f : F) (a b : G₀)

theorem map_inv₀ : f a⁻¹ = (f a)⁻¹ := by
  by_cases h : a = 0
  · simp [h, map_zero f]
  · apply eq_inv_of_mul_eq_one_left
    rw [← map_mul, inv_mul_cancel₀ h, map_one]

end

section

open scoped Ring

variable {M M₀ G₀ M₀' G₀' F F' : Type*}

variable [MonoidWithZero M₀]

variable [GroupWithZero G₀] [MulZeroOneClass M₀'] [Nontrivial M₀'] [FunLike F G₀ M₀']
  [MonoidWithZeroHomClass F G₀ M₀']
  (f : F) {a : G₀}

theorem map_ne_zero : f a ≠ 0 ↔ a ≠ 0 := by
  refine ⟨fun hfa ha => hfa <| ha.symm ▸ map_zero f, ?_⟩
  intro hx H
  lift a to G₀ˣ using isUnit_iff_ne_zero.mpr hx
  apply one_ne_zero (α := M₀')
  rw [← map_one f, ← Units.mul_inv a, map_mul, H, zero_mul]

end
