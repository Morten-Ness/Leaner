import Mathlib

variable {R : Type*}

variable {p q : R}

theorem zero [NonUnitalNonAssocSemiring R] [StarAddMonoid R] : IsStarProjection (0 : R) := ⟨.zero, .zero _⟩

