import Mathlib

variable {ι α : Type*} {R : ι → Type*}

variable [∀ i, Mul (R i)]

theorem isLeftRegular_iff {a : ∀ i, R i} : IsLeftRegular a ↔ ∀ i, IsLeftRegular (a i) := have (i : _) : Nonempty (R i) := ⟨a i⟩; Pi.map_injective

