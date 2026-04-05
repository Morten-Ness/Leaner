import Mathlib

variable {α β γ : Type*} {f g : α → β} {c c₁ c₂ x : α}

theorem Periodic.mul_const_inv [DivisionSemiring α] (h : Periodic f c) (a : α) :
    Periodic (fun x => f (x * a⁻¹)) (c * a) := h.const_inv_smul₀ (MulOpposite.op a)

