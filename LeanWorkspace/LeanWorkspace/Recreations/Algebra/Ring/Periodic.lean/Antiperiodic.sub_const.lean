import Mathlib

variable {α β γ : Type*} {f g : α → β} {c c₁ c₂ x : α}

theorem Antiperiodic.sub_const [SubtractionCommMonoid α] [Neg β] (h : Function.Antiperiodic f c) (a : α) :
    Function.Antiperiodic (fun x => f (x - a)) c := by
  simpa only [sub_eq_add_neg] using h.add_const (-a)

