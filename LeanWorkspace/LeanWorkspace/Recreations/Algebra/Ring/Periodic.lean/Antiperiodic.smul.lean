import Mathlib

variable {α β γ : Type*} {f g : α → β} {c c₁ c₂ x : α}

theorem Antiperiodic.smul [Add α] [Monoid γ] [AddGroup β] [DistribMulAction γ β]
    (h : Function.Antiperiodic f c) (a : γ) : Function.Antiperiodic (a • f) c := by simp_all

