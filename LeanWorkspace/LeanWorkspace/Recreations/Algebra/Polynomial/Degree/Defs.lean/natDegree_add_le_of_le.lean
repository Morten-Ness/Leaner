import Mathlib

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p : R[X]}

variable {p q : R[X]} {ι : Type*}

theorem natDegree_add_le_of_le (hp : Polynomial.natDegree p ≤ m) (hq : Polynomial.natDegree q ≤ n) :
    Polynomial.natDegree (p + q) ≤ max m n := (Polynomial.natDegree_add_le p q).trans <| max_le_max ‹_› ‹_›

