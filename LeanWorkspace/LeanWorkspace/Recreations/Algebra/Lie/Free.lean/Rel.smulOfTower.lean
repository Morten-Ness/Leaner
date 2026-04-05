import Mathlib

variable (R : Type u) (X : Type v) [CommRing R]

theorem Rel.smulOfTower {S : Type*} [Monoid S] [DistribMulAction S R] [IsScalarTower S R R] (t : S)
    (a b : lib R X) (h : Rel R X a b) : Rel R X (t • a) (t • b) := by
  rw [← smul_one_smul R t a, ← smul_one_smul R t b]
  exact h.smul _

