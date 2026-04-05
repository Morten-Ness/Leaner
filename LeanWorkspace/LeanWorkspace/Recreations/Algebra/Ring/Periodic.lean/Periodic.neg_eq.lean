import Mathlib

variable {α β γ : Type*} {f g : α → β} {c c₁ c₂ x : α}

theorem Periodic.neg_eq [AddGroup α] (h : Function.Periodic f c) : f (-c) = f 0 := h.neg.eq

