import Mathlib

variable (M α : Type*) [Monoid M]

variable [AddGroup α] [DistribMulAction M α]

theorem FixedPoints.mem_addSubgroup (a : α) : a ∈ α^+M ↔ ∀ m : M, m • a = a := Iff.rfl

