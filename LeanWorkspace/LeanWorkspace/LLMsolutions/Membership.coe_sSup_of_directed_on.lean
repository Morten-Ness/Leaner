FAIL
import Mathlib

variable {ι : Sort*} {M : Type*}

variable [Mul M]

theorem coe_sSup_of_directed_on {S : Set (Subsemigroup M)} (hS : DirectedOn (· ≤ ·) S) :
    (↑(sSup S) : Set M) = ⋃ s ∈ S, ↑s := by
  classical
  ext x
  simp only [Set.mem_iUnion, SetLike.mem_coe]
  constructor
  · intro hx
    change x ∈ sSup S at hx
    rw [Subsemigroup.sSup_eq_iSup] at hx
    simpa [iSup_subtype] using hx
  · rintro ⟨s, hsS, hxs⟩
    change x ∈ sSup S
    rw [Subsemigroup.sSup_eq_iSup]
    rw [iSup_subtype]
    exact ⟨s, hsS, hxs⟩
