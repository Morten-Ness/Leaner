import Mathlib

variable {M A B : Type*}

variable [MulOneClass M]

theorem coe_sSup_of_directedOn {S : Set (Submonoid M)} (Sne : S.Nonempty)
    (hS : DirectedOn (· ≤ ·) S) : (↑(sSup S) : Set M) = ⋃ s ∈ S, ↑s := by
  ext x
  constructor
  · intro hx
    change x ∈ sSup S at hx
    rw [Submonoid.mem_sSup_of_directedOn Sne hS] at hx
    simpa [Set.mem_iUnion] using hx
  · intro hx
    rw [Set.mem_iUnion] at hx
    rcases hx with ⟨s, hx⟩
    rw [Set.mem_iUnion] at hx
    rcases hx with ⟨hsS, hxs⟩
    change x ∈ sSup S
    rw [Submonoid.mem_sSup_of_directedOn Sne hS]
    exact ⟨s, hsS, hxs⟩
