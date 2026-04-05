import Mathlib

variable {M M₀ M₀' G₀ G₀' N A A' B α β : Type*}

variable {A} [Zero M₀] [Zero A] [SMulWithZero M₀ A]

theorem zero_smul (m : A) : (0 : M₀) • m = 0 := SMulWithZero.zero_smul m

