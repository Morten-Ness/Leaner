import Mathlib

variable {α β γ : Type*} {f g : α → β} {c c₁ c₂ x : α}

theorem Periodic.div [Add α] [Div β] (hf : Function.Periodic f c) (hg : Function.Periodic g c) :
    Function.Periodic (f / g) c := by simp_all

