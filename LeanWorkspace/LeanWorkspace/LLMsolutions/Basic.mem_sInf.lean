FAIL
import Mathlib

variable {K : Type u} {L : Type v} {M : Type w}

variable [DivisionRing K] [DivisionRing L] [DivisionRing M]

theorem mem_sInf {S : Set (Subfield K)} {x : K} : x ∈ sInf S ↔ ∀ p ∈ S, x ∈ p := by
  constructor
  · intro hx p hp
    exact show x ∈ p from (show sInf S ≤ p from sInf_le hp) hx
  · intro hx
    exact show x ∈ sInf S from mem_iInf.mp (by
      simpa [Set.mem_setOf_eq] using hx)
