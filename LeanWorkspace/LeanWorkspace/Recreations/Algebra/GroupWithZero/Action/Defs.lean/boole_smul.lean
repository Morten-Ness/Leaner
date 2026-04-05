import Mathlib

variable {M M₀ M₀' G₀ G₀' N A A' B α β : Type*}

variable (M₀ A) [MonoidWithZero M₀] [MonoidWithZero M₀'] [Zero A]

variable {M₀ A} [MulActionWithZero M₀ A] [Zero A'] [SMul M₀ A'] (p : Prop) [Decidable p]

theorem boole_smul (a : A) : (if p then 1 else 0 : M₀) • a = if p then a else 0 := by simp

