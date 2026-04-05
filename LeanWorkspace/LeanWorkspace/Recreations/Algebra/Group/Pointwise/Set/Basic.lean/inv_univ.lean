import Mathlib

variable {F α β γ : Type*}

variable {ι : Sort*} [Inv α] {s t : Set α} {a : α}

theorem inv_univ : (univ : Set α)⁻¹ = univ := rfl

