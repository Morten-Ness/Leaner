import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [DecidableEq α] [Inv α] {s t : Finset α} {a : α}

theorem sup'_inv [SemilatticeSup β] {s : Finset α} (hs : s⁻¹.Nonempty) (f : α → β) :
    sup' s⁻¹ hs f = sup' s hs.of_inv (f ·⁻¹) := sup'_image ..

