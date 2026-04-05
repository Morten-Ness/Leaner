import Mathlib

variable {M M₀ M₀' G₀ G₀' N A A' B α β : Type*}

variable {A} [Zero M₀] [Zero A] [SMulWithZero M₀ A]

variable {M₀} {a : M₀} {b : A}

theorem smul_eq_zero_of_left (h : a = 0) (b : A) : a • b = 0 := h.symm ▸ zero_smul _ b

