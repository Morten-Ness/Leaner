import Mathlib

variable {R S : Type*} (M : Type*) {a b : R} {s : S}

theorem IsRightRegular.isSMulRegular [Mul R] {c : R} (h : IsRightRegular c) :
    IsSMulRegular R (MulOpposite.op c) := h

