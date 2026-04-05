import Mathlib

variable {M N G H α β γ δ : Type*}

variable (G P : Type*)

theorem IsCancelSMul.right_cancel {G P} [SMul G P] [IsCancelSMul G P] (a b : G) (c : P) :
    a • c = b • c → a = b := IsCancelSMul.right_cancel' a b c

