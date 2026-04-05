import Mathlib

variable {M N G H α β γ δ : Type*}

variable (G P : Type*)

theorem IsCancelSMul.left_cancel {G P} [SMul G P] [IsCancelSMul G P] (a : G) (b c : P) :
    a • b = a • c → b = c := IsLeftCancelSMul.left_cancel' a b c

