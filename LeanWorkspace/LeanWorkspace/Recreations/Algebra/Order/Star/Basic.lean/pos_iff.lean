import Mathlib

open scoped NNRat

variable {R A : Type*}

variable [NonUnitalSemiring R] [PartialOrder R] [StarRing R]

variable [StarOrderedRing R] {x y : R}

theorem pos_iff : 0 < x ↔ x ≠ 0 ∧ x ∈ AddSubmonoid.closure (Set.range fun s : R => star s * s) := by
  simp [lt_iff_le_and_ne, and_comm, eq_comm, le_iff]

