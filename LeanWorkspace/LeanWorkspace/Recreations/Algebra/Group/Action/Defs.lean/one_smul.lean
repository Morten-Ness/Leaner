import Mathlib

variable {M N G H α β γ δ : Type*}

variable [Monoid M] [MulAction M α] {a : M}

theorem one_smul (b : α) : (1 : M) • b = b := MulAction.one_smul _

