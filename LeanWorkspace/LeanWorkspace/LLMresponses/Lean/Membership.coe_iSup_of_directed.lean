import Mathlib

variable {M A B : Type*}

variable [MulOneClass M]

theorem coe_iSup_of_directed {ι} [Nonempty ι] {S : ι → Submonoid M} (hS : Directed (· ≤ ·) S) :
    ((⨆ i, S i : Submonoid M) : Set M) = ⋃ i, S i := by
  ext x
  rw [Set.mem_iUnion]
  exact Submonoid.mem_iSup_of_directed hS
