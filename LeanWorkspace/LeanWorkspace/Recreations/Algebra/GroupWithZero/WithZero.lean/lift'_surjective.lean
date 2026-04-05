import Mathlib

variable {α β γ : Type*}

variable [MulOneClass α]

variable [MulZeroOneClass β]

theorem lift'_surjective {f : α →* β} (hf : Function.Surjective f) :
    Function.Surjective (lift' f) := by
  intro b
  obtain ⟨a, rfl⟩ := hf b
  exact ⟨a, by simp⟩

