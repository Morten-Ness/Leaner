import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b : R} {n m : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem natTrailingDegree_mul [NoZeroDivisors R] (hp : p ≠ 0) (hq : q ≠ 0) :
    (p * q).natTrailingDegree = p.natTrailingDegree + q.natTrailingDegree := Polynomial.natTrailingDegree_mul'
    (mul_ne_zero (mt Polynomial.trailingCoeff_eq_zero.mp hp) (mt Polynomial.trailingCoeff_eq_zero.mp hq))

