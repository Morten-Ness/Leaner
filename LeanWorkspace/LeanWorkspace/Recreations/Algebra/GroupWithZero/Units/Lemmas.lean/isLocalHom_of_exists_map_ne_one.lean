import Mathlib

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

