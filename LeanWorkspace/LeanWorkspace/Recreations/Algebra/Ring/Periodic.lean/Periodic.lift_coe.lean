import Mathlib

variable {α β γ : Type*} {f g : α → β} {c c₁ c₂ x : α}

theorem Periodic.lift_coe [AddGroup α] (h : Function.Periodic f c) (a : α) :
    h.lift (a : α ⧸ AddSubgroup.zmultiples c) = f a := rfl

