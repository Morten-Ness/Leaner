import Mathlib

variable {ι : Sort*} {M : Type*}

variable [Mul M]

theorem mem_sSup_of_directed_on {S : Set (Subsemigroup M)} (hS : DirectedOn (· ≤ ·) S) {x : M} :
    x ∈ sSup S ↔ ∃ s ∈ S, x ∈ s := by
  simp only [sSup_eq_iSup', Subsemigroup.mem_iSup_of_directed hS.directed_val, SetCoe.exists, exists_prop]

