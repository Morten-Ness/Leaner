FAIL
import Mathlib

variable {ι : Sort*} {M : Type*}

variable [Mul M]

theorem mem_sSup_of_directed_on {S : Set (Subsemigroup M)} (hS : DirectedOn (· ≤ ·) S) {x : M} :
    x ∈ sSup S ↔ ∃ s ∈ S, x ∈ s := by
  constructor
  · intro hx
    rw [Subsemigroup.mem_sSup_of_directedOn hS] at hx
    simpa using hx
  · rintro ⟨s, hs, hx⟩
    rw [Subsemigroup.mem_sSup_of_directedOn hS]
    exact ⟨s, hs, hx⟩
