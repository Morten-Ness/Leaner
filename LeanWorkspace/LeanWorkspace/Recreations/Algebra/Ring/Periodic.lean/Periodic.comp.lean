import Mathlib

variable {α β γ : Type*} {f g : α → β} {c c₁ c₂ x : α}

theorem Periodic.comp [Add α] (h : Function.Periodic f c) (g : β → γ) : Function.Periodic (g ∘ f) c := by
  simp_all

