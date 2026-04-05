import Mathlib

variable {M : Type*}

theorem mem_closure' [Semigroup M] {s : Set M} {x : M} :
    x ∈ closure s ↔ x ∈ s ∨ ∃ y, ∃ z ∈ s, y * z = x := by
  rw [← SetLike.mem_coe, SemigroupIdeal.coe_closure]
  simp [mem_mul]

attribute [inherit_doc AddSemigroupIdeal.coe_closure] AddSemigroupIdeal.mem_closure'

