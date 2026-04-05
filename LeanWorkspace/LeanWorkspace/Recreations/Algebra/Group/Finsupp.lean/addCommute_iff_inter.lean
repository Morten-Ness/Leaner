import Mathlib

variable {ι F M N O G H : Type*}

variable [AddZeroClass M] [AddZeroClass N] {f : M → N} {g₁ g₂ : ι →₀ M}

theorem addCommute_iff_inter [DecidableEq ι] {f g : ι →₀ M} :
    AddCommute f g ↔ ∀ x ∈ f.support ∩ g.support, AddCommute (f x) (g x) where
  mp h := fun x _ ↦ Finsupp.ext_iff.1 h x
  mpr h := by
    ext x
    by_cases hf : x ∈ f.support
    · by_cases hg : x ∈ g.support
      · exact h _ (mem_inter_of_mem hf hg)
      · simp_all
    · simp_all

