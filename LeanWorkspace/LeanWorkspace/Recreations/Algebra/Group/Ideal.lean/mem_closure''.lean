import Mathlib

variable {M : Type*}

theorem mem_closure'' [Monoid M] {s : Set M} {x : M} :
    x ∈ closure s ↔ ∃ y, ∃ z ∈ s, y * z = x := by
  rw [← SetLike.mem_coe, SemigroupIdeal.coe_closure']
  simp [mem_mul]

attribute [inherit_doc AddSemigroupIdeal.coe_closure'] AddSemigroupIdeal.mem_closure''

