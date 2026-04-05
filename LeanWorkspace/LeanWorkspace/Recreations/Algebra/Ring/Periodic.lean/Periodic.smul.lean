import Mathlib

variable {α β γ : Type*} {f g : α → β} {c c₁ c₂ x : α}

theorem Periodic.smul [Add α] [SMul γ β] (h : Function.Periodic f c) (a : γ) :
    Function.Periodic (a • f) c := by simp_all

