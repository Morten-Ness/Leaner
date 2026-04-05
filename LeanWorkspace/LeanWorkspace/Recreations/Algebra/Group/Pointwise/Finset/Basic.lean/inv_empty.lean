import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [DecidableEq α] [Inv α] {s t : Finset α} {a : α}

theorem inv_empty : (∅ : Finset α)⁻¹ = ∅ := rfl

