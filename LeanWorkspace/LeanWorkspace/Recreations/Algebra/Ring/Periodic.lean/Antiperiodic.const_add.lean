import Mathlib

variable {α β γ : Type*} {f g : α → β} {c c₁ c₂ x : α}

theorem Antiperiodic.const_add [AddSemigroup α] [Neg β] (h : Function.Antiperiodic f c) (a : α) :
    Function.Antiperiodic (fun x => f (a + x)) c := fun x => by simpa [add_assoc] using h (a + x)

