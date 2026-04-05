import Mathlib

variable {ι α : Type*} {R : ι → Type*}

variable [∀ i, Mul (R i)]

theorem isRightRegular_iff {a : ∀ i, R i} : IsRightRegular a ↔ ∀ i, IsRightRegular (a i) := have (i : _) : Nonempty (R i) := ⟨a i⟩; .symm <| Pi.map_injective.symm

