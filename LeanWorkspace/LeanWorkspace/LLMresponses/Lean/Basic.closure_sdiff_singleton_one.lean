import Mathlib

variable {M : Type*} {N : Type*}

variable {A : Type*}

variable [MulOneClass M] {s : Set M}

variable [AddZeroClass A] {t : Set A}

variable (S : Submonoid M)

variable {t : Set M}

theorem closure_sdiff_singleton_one (s : Set M) : Submonoid.closure (s \ {1}) = Submonoid.closure s := by
  apply le_antisymm
  · exact Submonoid.closure_mono (by
      intro x hx
      exact hx.1)
  · refine Submonoid.closure_le.2 ?_
    intro x hx
    by_cases h : x = 1
    · subst h
      exact Submonoid.one_mem _
    · exact Submonoid.subset_closure ⟨hx, by simpa [Set.mem_singleton_iff] using h⟩
