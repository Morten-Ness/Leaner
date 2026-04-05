import Mathlib

variable {α β γ : Type*} {f g : α → β} {c c₁ c₂ x : α}

theorem Antiperiodic.funext' [Add α] [InvolutiveNeg β] (h : Function.Antiperiodic f c) :
    (fun x => -f (x + c)) = f := neg_eq_iff_eq_neg.mpr h.funext

