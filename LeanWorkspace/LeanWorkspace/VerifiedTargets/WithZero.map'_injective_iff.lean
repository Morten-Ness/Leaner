import Mathlib

variable {α β γ : Type*}

variable [MulOneClass α]

variable [MulOneClass β] [MulOneClass γ]

theorem map'_injective_iff {f : α →* β} : Function.Injective (WithZero.map' f) ↔ Function.Injective f := by
  simp [Function.Injective, WithZero.forall]

alias ⟨_, map'_injective⟩ := map'_injective_iff

