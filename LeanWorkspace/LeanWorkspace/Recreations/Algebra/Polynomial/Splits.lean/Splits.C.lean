import Mathlib

variable {R : Type*}

variable [Semiring R]

theorem Splits.C (a : R) : Polynomial.Splits (C a) := Submonoid.mem_closure_of_mem (Set.mem_union_left _ ⟨a, rfl⟩)

