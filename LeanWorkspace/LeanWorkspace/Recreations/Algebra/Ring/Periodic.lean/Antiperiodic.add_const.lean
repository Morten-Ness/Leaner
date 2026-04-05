import Mathlib

variable {α β γ : Type*} {f g : α → β} {c c₁ c₂ x : α}

theorem Antiperiodic.add_const [AddCommSemigroup α] [Neg β] (h : Function.Antiperiodic f c) (a : α) :
    Function.Antiperiodic (fun x => f (x + a)) c := fun x => by
  simpa only [add_right_comm] using h (x + a)

