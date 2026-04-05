import Mathlib

variable {α β ι : Type*} {π : ι → Type*}

variable [KleeneAlgebra α] {a b c : α}

theorem kstar_mono : Monotone (KStar.kstar : α → α) := fun _ _ h ↦
    kstar_le_of_mul_le_left one_le_kstar <| kstar_mul_le (h.trans le_kstar) <| mul_kstar_le_kstar

