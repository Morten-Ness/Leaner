import Mathlib

variable {α β γ : Type*} {f g : α → β} {c c₁ c₂ x : α}

theorem Periodic.const_mul [DivisionSemiring α] (h : Periodic f c) (a : α) :
    Periodic (fun x => f (a * x)) (a⁻¹ * c) := Function.Periodic.const_smul₀ h a

