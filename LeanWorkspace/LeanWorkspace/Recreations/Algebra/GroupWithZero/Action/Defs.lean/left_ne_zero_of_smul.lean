import Mathlib

variable {M M₀ M₀' G₀ G₀' N A A' B α β : Type*}

variable {A} [Zero M₀] [Zero A] [SMulWithZero M₀ A]

variable {M₀} {a : M₀} {b : A}

theorem left_ne_zero_of_smul : a • b ≠ 0 → a ≠ 0 := mt fun h ↦ smul_eq_zero_of_left h b

