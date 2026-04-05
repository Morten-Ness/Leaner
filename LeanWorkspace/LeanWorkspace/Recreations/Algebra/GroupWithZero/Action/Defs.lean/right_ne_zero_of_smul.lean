import Mathlib

variable {M M₀ M₀' G₀ G₀' N A A' B α β : Type*}

variable [Zero A] [SMulZeroClass M A]

theorem right_ne_zero_of_smul {a : M} {b : A} : a • b ≠ 0 → b ≠ 0 := mt <| smul_eq_zero_of_right a

