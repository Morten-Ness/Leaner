import Mathlib

open scoped Polynomial

variable {Fq : Type*} [Field Fq] [Fintype Fq]

theorem cardPowDegree_apply [DecidableEq Fq] (p : Fq[X]) :
    Polynomial.cardPowDegree p = if p = 0 then 0 else (Fintype.card Fq : ℤ) ^ natDegree p := by
  simp [Polynomial.cardPowDegree]

