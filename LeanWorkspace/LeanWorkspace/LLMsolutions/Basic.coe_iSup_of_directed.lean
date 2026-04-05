import Mathlib

variable {K : Type u} {L : Type v} {M : Type w}

variable [DivisionRing K] [DivisionRing L] [DivisionRing M]

theorem coe_iSup_of_directed {ι} [hι : Nonempty ι] {S : ι → Subfield K} (hS : Directed (· ≤ ·) S) :
    ((⨆ i, S i : Subfield K) : Set K) = ⋃ i, ↑(S i) := by
  ext x
  simp only [Set.mem_iUnion]
  exact show x ∈ (⨆ i, S i) ↔ ∃ i, x ∈ S i by
    simpa using Subfield.mem_iSup_of_directed hS
