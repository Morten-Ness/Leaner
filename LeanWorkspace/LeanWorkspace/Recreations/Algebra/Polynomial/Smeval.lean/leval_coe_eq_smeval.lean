import Mathlib

variable (R : Type*) [Semiring R] (p q : R[X]) {S : Type*} [AddCommMonoid S] [Pow S ℕ] [Module R S]
  (x : S)

theorem leval_coe_eq_smeval {R : Type*} [Semiring R] (r : R) :
    ⇑(leval r) = fun p => p.smeval r := by
  ext
  simpa using Polynomial.eval_eq_smeval _ _

