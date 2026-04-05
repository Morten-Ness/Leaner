import Mathlib

variable {M N G H α β γ δ : Type*}

variable [Monoid M] [MulAction M α] {a : M}

theorem smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b := (mul_smul _ _ _).symm

