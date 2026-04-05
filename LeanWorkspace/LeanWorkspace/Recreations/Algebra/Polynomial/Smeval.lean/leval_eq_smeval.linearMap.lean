import Mathlib

variable (R : Type*) [Semiring R] (p q : R[X]) {S : Type*} [AddCommMonoid S] [Pow S ℕ] [Module R S]
  (x : S)

theorem leval_eq_smeval.linearMap {R : Type*} [Semiring R] (r : R) :
    leval r = Polynomial.smeval.linearMap R r := by
  refine LinearMap.ext ?_
  intro
  rw [leval_apply, Polynomial.smeval.linearMap_apply, Polynomial.eval_eq_smeval]

