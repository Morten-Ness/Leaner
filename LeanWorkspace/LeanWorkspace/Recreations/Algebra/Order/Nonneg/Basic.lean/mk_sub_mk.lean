import Mathlib

variable {α : Type*}

variable [Zero α] [SemilatticeSup α]

theorem mk_sub_mk [Sub α] {x y : α} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (⟨x, hx⟩ : { x : α // 0 ≤ x }) - ⟨y, hy⟩ = Nonneg.toNonneg (x - y) := rfl

