import Mathlib

variable {ι α β : Type*} {G M R : ι → Type*}

variable [∀ i, Star (R i)]

theorem star_def (x : ∀ i, R i) : star x = fun i => star (x i) := rfl

