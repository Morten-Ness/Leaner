import Mathlib

variable {M M₀ M₀' G₀ G₀' N A A' B α β : Type*}

variable [AddZeroClass A] [DistribSMul M A]

theorem smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂ := DistribSMul.smul_add _ _ _

