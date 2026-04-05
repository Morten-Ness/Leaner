import Mathlib

variable {M A B : Type*}

variable [MulOneClass M]

theorem coe_sSup_of_directedOn {S : Set (Submonoid M)} (Sne : S.Nonempty)
    (hS : DirectedOn (· ≤ ·) S) : (↑(sSup S) : Set M) = ⋃ s ∈ S, ↑s := Set.ext fun x => by simp [Submonoid.mem_sSup_of_directedOn Sne hS]

