import Mathlib

variable {α β γ : Type*} {f g : α → β} {c c₁ c₂ x : α}

theorem Periodic.mul_const [DivisionSemiring α] (h : Periodic f c) (a : α) :
    Periodic (fun x => f (x * a)) (c * a⁻¹) := h.const_smul₀ (MulOpposite.op a)

