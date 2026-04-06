FAIL
import Mathlib

variable {α β γ : Type*}

variable [MulOneClass α]

variable [MulOneClass β] [MulOneClass γ]

theorem map'_injective_iff {f : α →* β} : Function.Injective (WithZero.map' f) ↔ Function.Injective f := by
  constructor
  · intro h a b hab
    apply Option.some.inj
    apply h
    simpa using hab
  · intro h x y hxy
    cases x <;> cases y
    · rfl
    · rfl
    · rfl
    · simp only [WithZero.map'_eq_zero_iff, Option.map_eq_some'] at hxy ⊢
      exact h hxy
