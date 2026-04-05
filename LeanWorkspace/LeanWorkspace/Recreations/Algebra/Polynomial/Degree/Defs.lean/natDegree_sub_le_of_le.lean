import Mathlib

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Ring R] {p q : R[X]}

theorem natDegree_sub_le_of_le (hp : Polynomial.natDegree p ≤ m) (hq : Polynomial.natDegree q ≤ n) :
    Polynomial.natDegree (p - q) ≤ max m n := (Polynomial.natDegree_sub_le p q).trans <| max_le_max ‹_› ‹_›

