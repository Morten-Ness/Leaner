import Mathlib

variable {ι α β : Type*} {G M R : ι → Type*}

variable [∀ i, Star (R i)]

theorem star_apply (x : ∀ i, R i) (i : ι) : star x i = star (x i) := rfl

