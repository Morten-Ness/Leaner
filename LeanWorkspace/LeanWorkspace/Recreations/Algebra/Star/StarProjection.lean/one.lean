import Mathlib

variable {R : Type*}

variable {p q : R}

theorem one [MulOneClass R] [StarMul R] : IsStarProjection (1 : R) := ⟨.one, .one _⟩

