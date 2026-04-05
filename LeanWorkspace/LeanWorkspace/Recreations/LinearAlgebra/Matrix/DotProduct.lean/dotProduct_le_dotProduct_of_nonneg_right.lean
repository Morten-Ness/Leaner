import Mathlib

variable {m n p R : Type*}

variable [Semiring R] [PartialOrder R] [IsOrderedRing R] [Fintype n]

theorem dotProduct_le_dotProduct_of_nonneg_right {u v w : n → R} (huv : u ≤ v) (hw : 0 ≤ w) :
    u ⬝ᵥ w ≤ v ⬝ᵥ w := by
  unfold dotProduct; gcongr <;> apply_rules

