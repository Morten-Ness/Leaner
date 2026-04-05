import Mathlib

variable {α β γ : Type*} {f g : α → β} {c c₁ c₂ x : α}

theorem Antiperiodic.mul_const [DivisionSemiring α] [Neg β] (h : Antiperiodic f c) {a : α}
    (ha : a ≠ 0) : Antiperiodic (fun x => f (x * a)) (c * a⁻¹) := h.const_smul₀ <| (MulOpposite.op_ne_zero_iff a).mpr ha

