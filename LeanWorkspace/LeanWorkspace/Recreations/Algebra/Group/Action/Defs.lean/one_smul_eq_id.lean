import Mathlib

variable {M N G H α β γ δ : Type*}

variable [Monoid M] [MulAction M α] {a : M}

theorem one_smul_eq_id : (((1 : M) • ·) : α → α) = id := funext <| one_smul _

