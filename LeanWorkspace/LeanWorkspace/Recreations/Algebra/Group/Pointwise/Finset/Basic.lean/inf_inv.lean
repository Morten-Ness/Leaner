import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [DecidableEq α] [Inv α] {s t : Finset α} {a : α}

theorem inf_inv [SemilatticeInf β] [OrderTop β] (s : Finset α) (f : α → β) :
    inf s⁻¹ f = inf s (f ·⁻¹) := inf_image ..

