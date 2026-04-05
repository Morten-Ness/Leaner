import Mathlib

variable {α β γ : Type*} {f g : α → β} {c c₁ c₂ x : α}

theorem Antiperiodic.neg_eq [AddGroup α] [InvolutiveNeg β] (h : Function.Antiperiodic f c) :
    f (-c) = -f 0 := by
  simpa only [zero_add] using h.neg 0

