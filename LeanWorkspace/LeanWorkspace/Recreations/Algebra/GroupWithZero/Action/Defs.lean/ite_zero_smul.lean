import Mathlib

variable {M M₀ M₀' G₀ G₀' N A A' B α β : Type*}

variable (M₀ A) [MonoidWithZero M₀] [MonoidWithZero M₀'] [Zero A]

variable {M₀ A} [MulActionWithZero M₀ A] [Zero A'] [SMul M₀ A'] (p : Prop) [Decidable p]

theorem ite_zero_smul (a : M₀) (b : A) : (if p then a else 0 : M₀) • b = if p then a • b else 0 := by
  rw [ite_smul, zero_smul]

