import Mathlib

variable {R S : Type*} (M : Type*) {a b : R} {s : S}

theorem isLeftRegular_iff [Mul R] {a : R} : IsLeftRegular a ↔ IsSMulRegular R a := Iff.rfl

