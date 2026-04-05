import Mathlib

variable {ι F M N O G H : Type*}

variable [AddZeroClass M] [AddZeroClass N] {f : M → N} {g₁ g₂ : ι →₀ M}

variable [LinearOrder ι] {motive : (ι →₀ M) → Prop}

theorem induction_on_max₂ (f : ι →₀ M) (zero : motive 0)
    (add_single : ∀ a b (f : ι →₀ M), (∀ c ∈ f.support, c < a) → b ≠ 0 →
      motive f → motive (f + single a b)) : motive f := by
  classical
  refine Finsupp.induction_on_max f zero ?_
  convert add_single using 7 with _ _ _ H
  have := fun c hc ↦ (H c hc).ne
  apply (Finsupp.addCommute_of_disjoint _).eq
  simp_all [disjoint_iff_inter_eq_empty, eq_empty_iff_forall_notMem, single_apply, not_imp_not]

