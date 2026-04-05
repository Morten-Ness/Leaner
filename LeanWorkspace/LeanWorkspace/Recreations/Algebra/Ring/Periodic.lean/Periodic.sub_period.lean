import Mathlib

variable {α β γ : Type*} {f g : α → β} {c c₁ c₂ x : α}

theorem Periodic.sub_period [AddGroup α] (h1 : Function.Periodic f c₁) (h2 : Function.Periodic f c₂) :
    Function.Periodic f (c₁ - c₂) := fun x => by
  rw [sub_eq_add_neg, ← add_assoc, h2.neg, h1]

