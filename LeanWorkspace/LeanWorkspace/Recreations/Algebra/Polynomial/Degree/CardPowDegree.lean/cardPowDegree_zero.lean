import Mathlib

open scoped Polynomial

variable {Fq : Type*} [Field Fq] [Fintype Fq]

theorem cardPowDegree_zero : Polynomial.cardPowDegree (0 : Fq[X]) = 0 := rfl

