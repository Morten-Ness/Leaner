import Mathlib

variable {F α β γ : Type*}

variable {ι : Sort*} [Inv α] {s t : Set α} {a : α}

theorem inv_setOf (p : α → Prop) : {x | p x}⁻¹ = {x | p x⁻¹} := rfl

