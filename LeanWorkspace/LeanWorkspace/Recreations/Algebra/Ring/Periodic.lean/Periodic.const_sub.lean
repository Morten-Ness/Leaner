import Mathlib

variable {α β γ : Type*} {f g : α → β} {c c₁ c₂ x : α}

theorem Periodic.const_sub [AddCommGroup α] (h : Function.Periodic f c) (a : α) :
    Function.Periodic (fun x => f (a - x)) c := fun x => by
  simp only [← sub_sub, h.sub_eq]

