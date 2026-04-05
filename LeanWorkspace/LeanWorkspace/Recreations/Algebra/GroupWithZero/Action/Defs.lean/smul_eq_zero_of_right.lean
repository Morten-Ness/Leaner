import Mathlib

variable {M M₀ M₀' G₀ G₀' N A A' B α β : Type*}

variable [Zero A] [SMulZeroClass M A]

theorem smul_eq_zero_of_right (a : M) {b : A} (h : b = 0) : a • b = 0 := h.symm ▸ smul_zero a

