import Mathlib

variable {M : Type*} {S T : Set M}

variable [Monoid M]

theorem invOf_mem_center {a : M} [Invertible a] (ha : a ∈ Set.center M) : ⅟a ∈ Set.center M := by
  rw [Semigroup.mem_center_iff] at *
  exact (Commute.invOf_right <| ha ·)

