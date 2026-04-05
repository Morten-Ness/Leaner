import Mathlib

variable {α : Type*} {R : Type*} {M : Type*}

variable [Semiring R] [AddCommGroup M] [Module R M]

theorem mem_neg {g : M} {S : Submodule R M} : g ∈ -S ↔ -g ∈ S := Iff.rfl

