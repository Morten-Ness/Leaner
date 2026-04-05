import Mathlib

variable {M M₀ M₀' G₀ G₀' N A A' B α β : Type*}

variable [Zero A] [SMulZeroClass M A]

theorem smul_zero (a : M) : a • (0 : A) = 0 := SMulZeroClass.smul_zero _

