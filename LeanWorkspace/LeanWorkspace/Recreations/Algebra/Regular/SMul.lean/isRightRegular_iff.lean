import Mathlib

variable {R S : Type*} (M : Type*) {a b : R} {s : S}

theorem isRightRegular_iff [Mul R] {a : R} :
    IsRightRegular a ↔ IsSMulRegular R (MulOpposite.op a) := Iff.rfl

