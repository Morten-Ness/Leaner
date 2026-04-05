FAIL
import Mathlib

variable {K : Type u} {L : Type v} {M : Type w}

variable [DivisionRing K] [DivisionRing L] [DivisionRing M]

theorem coe_sInf (S : Set (Subfield K)) : ((sInf S : Subfield K) : Set K) = ⋂ s ∈ S, ↑s := by
  ext x
  simp only [Set.mem_iInter, Set.mem_setOf_eq]
  constructor
  · intro hx s
    simp only [Set.mem_iInter]
    intro hs
    exact hx hs
  · intro hx
    intro s hs
    exact hx s hs
