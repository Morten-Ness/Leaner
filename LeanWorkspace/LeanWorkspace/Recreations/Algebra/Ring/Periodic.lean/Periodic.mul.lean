import Mathlib

variable {α β γ : Type*} {f g : α → β} {c c₁ c₂ x : α}

theorem Periodic.mul [Add α] [Mul β] (hf : Function.Periodic f c) (hg : Function.Periodic g c) :
    Function.Periodic (f * g) c := by simp_all

