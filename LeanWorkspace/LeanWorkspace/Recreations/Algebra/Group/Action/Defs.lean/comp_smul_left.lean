import Mathlib

variable {M N G H α β γ δ : Type*}

variable [Monoid M] [MulAction M α] {a : M}

theorem comp_smul_left (a₁ a₂ : M) : (a₁ • ·) ∘ (a₂ • ·) = (((a₁ * a₂) • ·) : α → α) := funext fun _ ↦ (mul_smul _ _ _).symm

