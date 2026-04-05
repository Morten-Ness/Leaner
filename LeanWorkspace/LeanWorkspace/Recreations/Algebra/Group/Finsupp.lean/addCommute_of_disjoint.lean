import Mathlib

variable {ι F M N O G H : Type*}

variable [AddZeroClass M] [AddZeroClass N] {f : M → N} {g₁ g₂ : ι →₀ M}

theorem addCommute_of_disjoint {f g : ι →₀ M} (h : Disjoint f.support g.support) :
    AddCommute f g := by
  classical simp_all [Finsupp.addCommute_iff_inter, Finset.disjoint_iff_inter_eq_empty]

