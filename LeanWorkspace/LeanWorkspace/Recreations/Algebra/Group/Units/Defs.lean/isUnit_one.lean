import Mathlib

variable {α : Type u}

variable {M : Type*} {N : Type*}

theorem isUnit_one [Monoid M] : IsUnit (1 : M) := ⟨1, rfl⟩

