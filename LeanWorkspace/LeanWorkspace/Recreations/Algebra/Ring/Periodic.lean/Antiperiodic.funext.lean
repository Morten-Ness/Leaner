import Mathlib

variable {α β γ : Type*} {f g : α → β} {c c₁ c₂ x : α}

theorem Antiperiodic.funext [Add α] [Neg β] (h : Function.Antiperiodic f c) :
    (fun x => f (x + c)) = -f := funext h

