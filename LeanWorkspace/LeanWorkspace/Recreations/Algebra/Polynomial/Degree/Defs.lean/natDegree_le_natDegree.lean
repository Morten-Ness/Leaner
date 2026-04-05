import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem natDegree_le_natDegree [Semiring S] {q : S[X]} (hpq : p.degree ≤ q.degree) :
    p.natDegree ≤ q.natDegree := WithBot.giUnbotDBot.gc.monotone_l hpq

