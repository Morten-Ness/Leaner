import Mathlib

variable {ι F M N O G H : Type*}

variable [AddZeroClass M] [AddZeroClass N] {f : M → N} {g₁ g₂ : ι →₀ M}

theorem support_add_eq [DecidableEq ι] (h : Disjoint g₁.support g₂.support) :
    (g₁ + g₂).support = g₁.support ∪ g₂.support := le_antisymm support_zipWith fun a ha => by
    cases (Finset.mem_union_of_disjoint h).mp ha <;> simp_all

