import Mathlib

variable {α β γ : Type*} {f g : α → β} {c c₁ c₂ x : α}

theorem Periodic.mul_const' [DivisionSemiring α] (h : Periodic f c) (a : α) :
    Periodic (fun x => f (x * a)) (c / a) := by simpa only [div_eq_mul_inv] using h.mul_const a

