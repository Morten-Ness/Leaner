import Mathlib

variable {α β γ : Type*} {f g : α → β} {c c₁ c₂ x : α}

theorem Periodic.sub_const [SubtractionCommMonoid α] (h : Function.Periodic f c) (a : α) :
    Function.Periodic (fun x => f (x - a)) c := by
  simpa only [sub_eq_add_neg] using h.add_const (-a)

