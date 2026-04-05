import Mathlib

variable {R S : Type*} (M : Type*) {a b : R} {s : S}

variable [SMul R M] [SMul R S] [SMul S M] [IsScalarTower R S M]

theorem isLeftRegular [Mul R] {a : R} (h : IsSMulRegular R a) : IsLeftRegular a := h

