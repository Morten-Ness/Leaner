import Mathlib

open scoped NNRat

variable {R A : Type*}

variable [NonUnitalSemiring R] [PartialOrder R] [StarRing R]

variable [StarOrderedRing R] {x y : R}

theorem nonneg_iff : 0 ≤ x ↔ x ∈ AddSubmonoid.closure (Set.range fun s : R => star s * s) := by
  simp only [le_iff, zero_add, exists_eq_right']

