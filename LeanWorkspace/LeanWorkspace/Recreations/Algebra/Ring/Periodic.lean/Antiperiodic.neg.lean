import Mathlib

variable {α β γ : Type*} {f g : α → β} {c c₁ c₂ x : α}

theorem Antiperiodic.neg [AddGroup α] [InvolutiveNeg β] (h : Function.Antiperiodic f c) :
    Function.Antiperiodic f (-c) := by simpa only [sub_eq_add_neg, Function.Antiperiodic] using h.sub_eq

