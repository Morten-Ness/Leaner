import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [DecidableEq β] [Group α] [MulAction α β] {s t : Finset β} {a : α} {b : β}

theorem smul_finset_univ [Fintype β] : a • (univ : Finset β) = univ := image_univ_of_surjective <| MulAction.surjective a

