import Mathlib

variable {α β γ : Type*} {f g : α → β} {c c₁ c₂ x : α}

theorem Periodic.const_add [AddSemigroup α] (h : Function.Periodic f c) (a : α) :
    Function.Periodic (fun x => f (a + x)) c := fun x => by simpa [add_assoc] using h (a + x)

