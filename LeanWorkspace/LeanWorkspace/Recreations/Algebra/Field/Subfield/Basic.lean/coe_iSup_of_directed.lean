import Mathlib

variable {K : Type u} {L : Type v} {M : Type w}

variable [DivisionRing K] [DivisionRing L] [DivisionRing M]

theorem coe_iSup_of_directed {ι} [hι : Nonempty ι] {S : ι → Subfield K} (hS : Directed (· ≤ ·) S) :
    ((⨆ i, S i : Subfield K) : Set K) = ⋃ i, ↑(S i) := Set.ext fun x => by simp [Subfield.mem_iSup_of_directed hS]

