FAIL
import Mathlib

variable {K : Type u} {L : Type v} {M : Type w}

variable [DivisionRing K] [DivisionRing L] [DivisionRing M]

theorem coe_sSup_of_directedOn {S : Set (Subfield K)} (Sne : S.Nonempty)
    (hS : DirectedOn (· ≤ ·) S) : (↑(sSup S) : Set K) = ⋃ s ∈ S, ↑s := by
  ext x
  simp only [Set.mem_iUnion]
  constructor
  · intro hx
    exact (Subfield.mem_sSup_of_directedOn Sne hS).mp hx
  · intro hx
    exact (Subfield.mem_sSup_of_directedOn Sne hS).mpr hx
