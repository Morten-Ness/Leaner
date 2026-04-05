import Mathlib

variable {R : Type*}

variable [Monoid R] [StarMul R]

theorem _root_.isStarNormal_of_mem_unitary {u : R} (hu : u ∈ unitary R) : IsStarNormal u := coe_isStarNormal ⟨u, hu⟩

