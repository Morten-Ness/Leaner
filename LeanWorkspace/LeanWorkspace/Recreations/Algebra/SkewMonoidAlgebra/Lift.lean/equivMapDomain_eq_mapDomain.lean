import Mathlib

variable {k G H : Type*}

variable [AddCommMonoid k]

theorem equivMapDomain_eq_mapDomain (f : G ≃ H) (l : SkewMonoidAlgebra k G) :
    SkewMonoidAlgebra.equivMapDomain f l = mapDomain f l := by
  apply toFinsupp_injective
  ext x
  simp_rw [SkewMonoidAlgebra.toFinsupp_equivMapDomain, Finsupp.equivMapDomain_apply, toFinsupp_mapDomain,
    Finsupp.mapDomain_equiv_apply]

