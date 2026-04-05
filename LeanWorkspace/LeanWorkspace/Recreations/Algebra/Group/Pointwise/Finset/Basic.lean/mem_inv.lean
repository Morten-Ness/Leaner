import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [DecidableEq α] [Inv α] {s t : Finset α} {a : α}

theorem mem_inv {x : α} : x ∈ s⁻¹ ↔ ∃ y ∈ s, y⁻¹ = x := mem_image

