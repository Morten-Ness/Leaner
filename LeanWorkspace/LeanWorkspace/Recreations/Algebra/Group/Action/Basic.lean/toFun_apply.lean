import Mathlib

variable {G M A B α β : Type*}

variable [Monoid M] [MulAction M α]

theorem toFun_apply (x : M) (y : α) : MulAction.toFun M α y x = x • y := rfl

