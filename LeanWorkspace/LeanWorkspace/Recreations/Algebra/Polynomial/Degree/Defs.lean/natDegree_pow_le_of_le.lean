import Mathlib

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p : R[X]}

variable {p q : R[X]} {ι : Type*}

theorem natDegree_pow_le_of_le (n : ℕ) (hp : Polynomial.natDegree p ≤ m) :
    Polynomial.natDegree (p ^ n) ≤ n * m := Polynomial.natDegree_pow_le.trans (Nat.mul_le_mul le_rfl ‹_›)

