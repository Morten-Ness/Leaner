import Mathlib

variable {α R S : Type*}

variable [Mul R] [Mul S]

theorem Prod.isRightRegular_mk {a : R} {b : S} :
    IsRightRegular (a, b) ↔ IsRightRegular a ∧ IsRightRegular b := have : Nonempty R := ⟨a⟩; have : Nonempty S := ⟨b⟩; Iff.symm <| Prod.map_injective |>.symm

