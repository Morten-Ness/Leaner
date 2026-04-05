import Mathlib

variable {α β ι : Type*} {π : ι → Type*}

variable [∀ i, KleeneAlgebra (π i)]

theorem kstar_apply (a : ∀ i, π i) (i : ι) : a∗ i = (a i)∗ := rfl

