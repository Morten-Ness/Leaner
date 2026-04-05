import Mathlib

variable {R R' A T B ι : Type*}

variable [Semiring R] [Ring R']

variable [SemilatticeSup B] [OrderBot B] (D : A → B)

theorem apply_eq_zero_of_not_le_supDegree {p : R[A]} {a : A} (hlt : ¬ D a ≤ p.supDegree D) :
    p a = 0 := by
  contrapose! hlt
  exact Finset.le_sup (Finsupp.mem_support_iff.2 hlt)

