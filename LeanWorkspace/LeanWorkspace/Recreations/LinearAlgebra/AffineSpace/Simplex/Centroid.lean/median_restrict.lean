import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [DivisionRing k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {n : ℕ}

variable [NeZero n]

theorem median_restrict [CharZero k] (s : Affine.Simplex k P n) (i : Fin (n + 1)) (S : AffineSubspace k P)
    (hS : affineSpan k (Set.range s.points) ≤ S) :
    haveI := Nonempty.map (AffineSubspace.inclusion hS) inferInstance
    AffineSubspace.map (AffineSubspace.subtype S) ((s.restrict S hS).median i) = s.median i := by
  simp [Affine.Simplex.median, map_span, Set.image_pair]

