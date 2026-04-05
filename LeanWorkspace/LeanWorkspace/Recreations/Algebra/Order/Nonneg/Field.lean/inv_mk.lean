import Mathlib

variable {α : Type*}

variable [Semifield α] [LinearOrder α] [IsStrictOrderedRing α] {x y : α}

theorem inv_mk (hx : 0 ≤ x) :
    (⟨x, hx⟩ : { x : α // 0 ≤ x })⁻¹ = ⟨x⁻¹, inv_nonneg.2 hx⟩ := rfl

