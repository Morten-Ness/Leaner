import Mathlib

variable {k G H : Type*}

variable [AddCommMonoid k]

theorem equivMapDomain_single (f : G ≃ H) (a : G) (b : k) :
    SkewMonoidAlgebra.equivMapDomain f (single a b) = single (f a) b := by
  classical
  apply toFinsupp_injective
  simp_rw [SkewMonoidAlgebra.toFinsupp_equivMapDomain, single, Finsupp.equivMapDomain_single]

