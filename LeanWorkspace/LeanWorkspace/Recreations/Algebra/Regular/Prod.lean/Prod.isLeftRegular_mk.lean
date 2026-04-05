import Mathlib

variable {α R S : Type*}

variable [Mul R] [Mul S]

theorem Prod.isLeftRegular_mk {a : R} {b : S} :
    IsLeftRegular (a, b) ↔ IsLeftRegular a ∧ IsLeftRegular b := have : Nonempty R := ⟨a⟩; have : Nonempty S := ⟨b⟩; Prod.map_injective

