import Mathlib

variable {α β γ : Type*} {f g : α → β} {c c₁ c₂ x : α}

theorem Antiperiodic.const_mul [DivisionSemiring α] [Neg β] (h : Antiperiodic f c) {a : α}
    (ha : a ≠ 0) : Antiperiodic (fun x => f (a * x)) (a⁻¹ * c) := h.const_smul₀ ha

