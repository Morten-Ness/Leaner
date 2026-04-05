import Mathlib

variable (R : Type*) [Semiring R] (p q : R[X]) {S : Type*} [AddCommMonoid S] [Pow S ℕ] [Module R S]
  (x : S)

theorem smeval.linearMap_apply : Polynomial.smeval.linearMap R x p = p.smeval x := rfl

