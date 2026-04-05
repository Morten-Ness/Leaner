import Mathlib

open scoped NNRat

variable {R A : Type*}

variable [NonUnitalSemiring R] [PartialOrder R] [StarRing R]

variable [StarOrderedRing R] {x y : R}

variable [IsCancelAdd R]

theorem lt_iff :
    x < y ↔ ∃ p ≠ 0, p ∈ AddSubmonoid.closure (Set.range fun s => star s * s) ∧ y = x + p := by
  rw [lt_iff_le_and_ne, and_comm, StarOrderedRing.le_iff, ← exists_and_left]
  congr! 2 with p
  simp +contextual [← and_assoc]

