import Mathlib

variable {M M₀ M₀' G₀ G₀' N A A' B α β : Type*}

variable [Zero A] [SMulZeroClass M A]

theorem smul_ite_zero (p : Prop) [Decidable p] (a : M) (b : A) :
    (a • if p then b else 0) = if p then a • b else 0 := by split_ifs <;> simp

