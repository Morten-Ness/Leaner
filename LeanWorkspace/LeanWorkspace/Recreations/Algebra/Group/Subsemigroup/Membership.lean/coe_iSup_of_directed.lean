import Mathlib

variable {ι : Sort*} {M : Type*}

variable [Mul M]

theorem coe_iSup_of_directed {S : ι → Subsemigroup M} (hS : Directed (· ≤ ·) S) :
    ((⨆ i, S i : Subsemigroup M) : Set M) = ⋃ i, S i := Set.ext fun x => by simp [Subsemigroup.mem_iSup_of_directed hS]

