FAIL
import Mathlib

variable {ι F M N O G H : Type*}

variable [AddZeroClass M] [AddZeroClass N] {f : M → N} {g₁ g₂ : ι →₀ M}

theorem addCommute_of_disjoint {f g : ι →₀ M} (h : Disjoint f.support g.support) :
    AddCommute f g := by
  classical
  ext i
  by_cases hf : f i = 0
  · by_cases hg : g i = 0
    · rw [Finsupp.add_apply, Finsupp.add_apply, hf, hg]
    · have hfi : i ∉ f.support := by
        simpa [Finsupp.mem_support_iff] using hf
      have hgi : i ∈ g.support := by
        simpa [Finsupp.mem_support_iff] using hg
      exfalso
      exact (Finset.disjoint_left.1 h hgi hfi)
  · by_cases hg : g i = 0
    · rw [Finsupp.add_apply, Finsupp.add_apply, hf, hg, add_zero, zero_add]
    · have hfi : i ∈ f.support := by
        simpa [Finsupp.mem_support_iff] using hf
      have hgi : i ∈ g.support := by
        simpa [Finsupp.mem_support_iff] using hg
      exfalso
      exact (Finset.disjoint_left.1 h hfi hgi)
