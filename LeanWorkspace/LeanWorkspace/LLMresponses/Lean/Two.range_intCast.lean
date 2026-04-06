FAIL
import Mathlib

variable {R ι : Type*}

variable [Ring R] [CharP R 2]

theorem range_intCast : Set.range ((↑) : ℤ → R) = {0, 1} := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    rcases Int.even_or_odd z with ⟨k, hk⟩ | ⟨k, hk⟩
    · left
      rw [hk, ← Int.cast_add, add_self_eq_zero]
    · right
      rw [hk, Int.cast_add, Int.cast_ofNat, add_right_eq_self]
      exact add_self_eq_zero (↑k)
  · intro hx
    simp at hx
    rcases hx with rfl | rfl
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp⟩
