import Mathlib

variable {α β γ : Type*} {f g : α → β} {c c₁ c₂ x : α}

theorem Antiperiodic.div [Add α] [DivisionMonoid β] [HasDistribNeg β] (hf : Function.Antiperiodic f c)
    (hg : Function.Antiperiodic g c) : Function.Periodic (f / g) c := by simp_all [neg_div_neg_eq]

