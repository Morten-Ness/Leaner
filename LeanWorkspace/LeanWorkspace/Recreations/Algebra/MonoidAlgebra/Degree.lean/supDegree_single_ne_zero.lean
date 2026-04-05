import Mathlib

variable {R R' A T B ι : Type*}

variable [Semiring R] [Ring R']

variable [SemilatticeSup B] [OrderBot B] (D : A → B)

theorem supDegree_single_ne_zero (a : A) {r : R} (hr : r ≠ 0) :
    (single a r).supDegree D = D a := by
  rw [supDegree, Finsupp.support_single_ne_zero a hr, Finset.sup_singleton]

