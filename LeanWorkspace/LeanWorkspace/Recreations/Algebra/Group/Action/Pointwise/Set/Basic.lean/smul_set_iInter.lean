import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [Group α] [MulAction α β] {s t A B : Set β} {a b : α} {x : β}

theorem smul_set_iInter {ι : Sort*}
    (a : α) (t : ι → Set β) : (a • ⋂ i, t i) = ⋂ i, a • t i := image_iInter (MulAction.bijective a) t

