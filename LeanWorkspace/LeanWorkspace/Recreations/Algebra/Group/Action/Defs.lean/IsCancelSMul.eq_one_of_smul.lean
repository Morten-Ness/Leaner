import Mathlib

variable {M N G H α β γ δ : Type*}

variable (G P : Type*)

theorem IsCancelSMul.eq_one_of_smul {G P} [Monoid G] [MulAction G P] [IsCancelSMul G P] {g : G}
    {x : P} (h : g • x = x) : g = 1 := IsCancelSMul.right_cancel g 1 x ((one_smul G x).symm ▸ h)

