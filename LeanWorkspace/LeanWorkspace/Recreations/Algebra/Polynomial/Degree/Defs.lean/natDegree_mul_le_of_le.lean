import Mathlib

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p : R[X]}

variable {p q : R[X]} {ι : Type*}

theorem natDegree_mul_le_of_le (hp : Polynomial.natDegree p ≤ m) (hg : Polynomial.natDegree q ≤ n) :
    Polynomial.natDegree (p * q) ≤ m + n := Polynomial.natDegree_mul_le.trans <| add_le_add ‹_› ‹_›

