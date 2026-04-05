import Mathlib

variable {α β γ : Type*} {f g : α → β} {c c₁ c₂ x : α}

theorem Antiperiodic.mul_const_inv [DivisionSemiring α] [Neg β] (h : Antiperiodic f c) {a : α}
    (ha : a ≠ 0) : Antiperiodic (fun x => f (x * a⁻¹)) (c * a) := h.const_inv_smul₀ <| (MulOpposite.op_ne_zero_iff a).mpr ha

