import Mathlib

variable (M α : Type*) [Monoid M]

variable [AddMonoid α] [DistribMulAction M α]

theorem FixedPoints.mem_addSubmonoid (a : α) : a ∈ addSubmonoid M α ↔ ∀ m : M, m • a = a := Iff.rfl

