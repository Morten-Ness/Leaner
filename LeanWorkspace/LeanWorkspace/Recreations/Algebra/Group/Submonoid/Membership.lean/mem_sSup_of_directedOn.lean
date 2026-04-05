import Mathlib

variable {M A B : Type*}

variable [MulOneClass M]

theorem mem_sSup_of_directedOn {S : Set (Submonoid M)} (Sne : S.Nonempty)
    (hS : DirectedOn (· ≤ ·) S) {x : M} : x ∈ sSup S ↔ ∃ s ∈ S, x ∈ s := by
  haveI : Nonempty S := Sne.to_subtype
  simp [sSup_eq_iSup', Submonoid.mem_iSup_of_directed hS.directed_val]

