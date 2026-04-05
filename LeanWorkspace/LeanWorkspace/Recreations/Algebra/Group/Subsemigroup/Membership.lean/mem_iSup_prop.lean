import Mathlib

variable {ι : Sort*} {M : Type*}

variable [Mul M]

theorem mem_iSup_prop {p : Prop} {S : p → Subsemigroup M} {x : M} :
    x ∈ ⨆ (h : p), S h ↔ ∃ (h : p), x ∈ S h := by
  by_cases h : p
  · simp +contextual [h]
  · simpa [h] using id

