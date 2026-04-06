import Mathlib

variable {M : Type*} {N : Type*}

variable {A : Type*}

variable [MulOneClass M] {s : Set M}

variable [AddZeroClass A] {t : Set A}

variable (S : Submonoid M)

variable {t : Set M}

theorem closure_sdiff_eq_closure (hts : t ⊆ Submonoid.closure (s \ t)) : Submonoid.closure (s \ t) = Submonoid.closure s := by
  apply le_antisymm
  · exact Submonoid.closure_mono (by intro x hx; exact hx.1)
  · refine Submonoid.closure_le.2 ?_
    intro x hx
    by_cases hxt : x ∈ t
    · exact hts hxt
    · exact Submonoid.subset_closure ⟨hx, hxt⟩
