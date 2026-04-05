import Mathlib

variable {M N G H α β γ δ : Type*}

variable (G P : Type*)

theorem IsLeftCancelSMul.left_cancel {G P} [SMul G P] [IsLeftCancelSMul G P] (a : G) (b c : P) :
    a • b = a • c → b = c := IsLeftCancelSMul.left_cancel' a b c

