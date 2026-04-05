import Mathlib

variable {α : Type*}

variable [Semifield α] [LinearOrder α] [IsStrictOrderedRing α] {x y : α}

theorem mk_div_mk (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (⟨x, hx⟩ : { x : α // 0 ≤ x }) / ⟨y, hy⟩ = ⟨x / y, div_nonneg hx hy⟩ := rfl

