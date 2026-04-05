import Mathlib

variable {R S : Type*} (M : Type*) {a b : R} {s : S}

theorem IsLeftRegular.isSMulRegular [Mul R] {c : R} (h : IsLeftRegular c) : IsSMulRegular R c := h

