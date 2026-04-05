import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [DecidableEq α] [Inv α] {s t : Finset α} {a : α}

theorem sup_inv [SemilatticeSup β] [OrderBot β] (s : Finset α) (f : α → β) :
    sup s⁻¹ f = sup s (f ·⁻¹) := sup_image ..

