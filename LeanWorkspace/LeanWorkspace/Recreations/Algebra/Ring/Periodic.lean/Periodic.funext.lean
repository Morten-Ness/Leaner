import Mathlib

variable {α β γ : Type*} {f g : α → β} {c c₁ c₂ x : α}

theorem Periodic.funext [Add α] (h : Function.Periodic f c) : (fun x => f (x + c)) = f := funext h

