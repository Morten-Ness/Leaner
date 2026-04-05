import Mathlib

variable {R M : Type*}

variable [CommSemiring R] [AddCommMonoid M] [Module R M] (s : Set R) (a : R)

theorem mem_torsionBy_iff (x : M) : x ∈ Submodule.torsionBy R M a ↔ a • x = 0 := Iff.rfl

