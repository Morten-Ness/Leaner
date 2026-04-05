import Mathlib

variable {ι : Sort*} {M : Type*}

variable [Mul M]

theorem coe_sSup_of_directed_on {S : Set (Subsemigroup M)} (hS : DirectedOn (· ≤ ·) S) :
    (↑(sSup S) : Set M) = ⋃ s ∈ S, ↑s := Set.ext fun x => by simp [Subsemigroup.mem_sSup_of_directed_on hS]

