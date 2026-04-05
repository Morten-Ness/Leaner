import Mathlib

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem degree_le_natDegree : Polynomial.degree p ≤ Polynomial.natDegree p := WithBot.giUnbotDBot.gc.le_u_l _

