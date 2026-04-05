import Mathlib

variable {R : Type*}

variable [Semiring R]

theorem Splits.X_add_C (a : R) : Polynomial.Splits (X + C a) := Submonoid.mem_closure_of_mem (Set.mem_union_right _ ⟨a, rfl⟩)

