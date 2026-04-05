import Mathlib

variable {α β γ : Type*} {f g : α → β} {c c₁ c₂ x : α}

theorem Antiperiodic.const_sub [AddCommGroup α] [InvolutiveNeg β] (h : Function.Antiperiodic f c) (a : α) :
    Function.Antiperiodic (fun x => f (a - x)) c := fun x => by
  simp only [← sub_sub, h.sub_eq]

