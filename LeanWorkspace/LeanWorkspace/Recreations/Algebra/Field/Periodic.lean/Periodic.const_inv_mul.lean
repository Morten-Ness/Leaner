import Mathlib

variable {α β γ : Type*} {f g : α → β} {c c₁ c₂ x : α}

theorem Periodic.const_inv_mul [DivisionSemiring α] (h : Periodic f c) (a : α) :
    Periodic (fun x => f (a⁻¹ * x)) (a * c) := h.const_inv_smul₀ a

