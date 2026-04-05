import Mathlib

variable {α : Type u}

variable {M : Type*} {N : Type*}

theorem Units.isUnit [Monoid M] (u : Mˣ) : IsUnit (u : M) := ⟨u, rfl⟩

