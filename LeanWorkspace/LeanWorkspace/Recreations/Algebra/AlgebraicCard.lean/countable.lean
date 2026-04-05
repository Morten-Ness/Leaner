import Mathlib

variable (R : Type u) (A : Type v) [CommRing R] [IsDomain R] [CommRing A] [IsDomain A] [Algebra R A]
  [Module.IsTorsionFree R A]

variable [Countable R]

theorem countable : Set.Countable { x : A | IsAlgebraic R x } := by
  rw [← le_aleph0_iff_set_countable, ← lift_le_aleph0]
  apply (Algebraic.cardinalMk_lift_le_max R A).trans
  simp

