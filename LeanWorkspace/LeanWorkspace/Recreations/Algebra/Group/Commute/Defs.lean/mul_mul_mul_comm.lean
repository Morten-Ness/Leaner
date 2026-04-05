import Mathlib

variable {G M S : Type*}

variable [Semigroup S] {a b c : S}

theorem mul_mul_mul_comm (hbc : Commute b c) (a d : S) :
    a * b * (c * d) = a * c * (b * d) := by simp only [Commute.left_comm hbc, mul_assoc]

