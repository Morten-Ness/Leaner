import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [DecidableEq α] [Inv α] {s t : Finset α} {a : α}

theorem inf'_inv [SemilatticeInf β] {s : Finset α} (hs : s⁻¹.Nonempty) (f : α → β) :
    inf' s⁻¹ hs f = inf' s hs.of_inv (f ·⁻¹) := inf'_image ..

