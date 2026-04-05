import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [DivisionRing k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {n : ℕ}

variable [NeZero n]

theorem medial_restrict [CharZero k] (s : Affine.Simplex k P n) (S : AffineSubspace k P)
    (hS : affineSpan k (Set.range s.points) ≤ S) :
    haveI := Nonempty.map (AffineSubspace.inclusion hS) inferInstance
    (s.restrict S hS).medial = s.medial.restrict S (Affine.Simplex.affineSpan_range_medial s ▸ hS) := by
  haveI := Nonempty.map (AffineSubspace.inclusion hS) inferInstance
  ext i
  simp [Affine.Simplex.medial_points]

