import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [DecidableEq α] [Inv α] {s t : Finset α} {a : α}

theorem inv_singleton (a : α) : ({a} : Finset α)⁻¹ = {a⁻¹} := image_singleton _ _

