import Mathlib

open scoped Polynomial

variable {Fq : Type*} [Field Fq] [Fintype Fq]

theorem cardPowDegree_nonzero (p : Fq[X]) (hp : p ≠ 0) :
    Polynomial.cardPowDegree p = (Fintype.card Fq : ℤ) ^ p.natDegree := if_neg hp

