import Mathlib

variable {α β γ : Type*} {f g : α → β} {c c₁ c₂ x : α}

theorem Periodic.add_const [AddCommSemigroup α] (h : Function.Periodic f c) (a : α) :
    Function.Periodic (fun x => f (x + a)) c := fun x => by
  simpa only [add_right_comm] using h (x + a)

