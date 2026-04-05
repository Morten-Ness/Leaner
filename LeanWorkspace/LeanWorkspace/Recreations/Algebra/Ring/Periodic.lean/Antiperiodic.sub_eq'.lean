import Mathlib

variable {α β γ : Type*} {f g : α → β} {c c₁ c₂ x : α}

theorem Antiperiodic.sub_eq' [SubtractionCommMonoid α] [Neg β] (h : Function.Antiperiodic f c) :
    f (c - x) = -f (-x) := by simpa only [sub_eq_neg_add] using h (-x)

