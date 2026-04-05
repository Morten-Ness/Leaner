import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [Group α] [MulAction α β] {s t A B : Set β} {a b : α} {x : β}

theorem smul_set_univ : a • (univ : Set β) = univ := image_univ_of_surjective <| MulAction.surjective a

