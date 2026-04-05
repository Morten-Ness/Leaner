import Mathlib

variable {α : Type u}

variable {M : Type*}

theorem isUnit_of_subsingleton [Monoid M] [Subsingleton M] (a : M) : IsUnit a := ⟨⟨a, a, by subsingleton, by subsingleton⟩, rfl⟩

