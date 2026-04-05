import Mathlib

variable {α β γ : Type*} {f g : α → β} {c c₁ c₂ x : α}

theorem Antiperiodic.mul [Add α] [Mul β] [HasDistribNeg β] (hf : Function.Antiperiodic f c)
    (hg : Function.Antiperiodic g c) : Function.Periodic (f * g) c := by simp_all

