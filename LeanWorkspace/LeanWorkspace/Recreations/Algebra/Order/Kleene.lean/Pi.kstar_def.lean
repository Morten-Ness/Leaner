import Mathlib

variable {α β ι : Type*} {π : ι → Type*}

variable [∀ i, KleeneAlgebra (π i)]

theorem kstar_def (a : ∀ i, π i) : a∗ = fun i ↦ (a i)∗ := rfl

