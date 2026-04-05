import Mathlib

variable {ι F M N O G H : Type*}

variable [AddZeroClass M] [AddZeroClass N] {f : M → N} {g₁ g₂ : ι →₀ M}

theorem induction₂ {motive : (ι →₀ M) → Prop} (f : ι →₀ M) (zero : motive 0)
    (add_single : ∀ (a b) (f : ι →₀ M),
      a ∉ f.support → b ≠ 0 → motive f → motive (f + single a b)) : motive f := by
  classical
  refine f.induction zero ?_
  convert add_single using 7
  apply (Finsupp.addCommute_of_disjoint _).eq
  simp_all [disjoint_iff_inter_eq_empty, eq_empty_iff_forall_notMem, single_apply]

