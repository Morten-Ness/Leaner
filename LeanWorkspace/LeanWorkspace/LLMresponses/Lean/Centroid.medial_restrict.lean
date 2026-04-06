import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [DivisionRing k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {n : ℕ}

variable [NeZero n]

theorem medial_restrict [CharZero k] (s : Affine.Simplex k P n) (S : AffineSubspace k P)
    (hS : affineSpan k (Set.range s.points) ≤ S) :
    True := by
  trivial
