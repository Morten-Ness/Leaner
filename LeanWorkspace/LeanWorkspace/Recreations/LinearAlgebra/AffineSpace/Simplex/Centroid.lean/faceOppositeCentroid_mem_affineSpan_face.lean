import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [DivisionRing k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {n : ℕ}

variable [NeZero n]

theorem faceOppositeCentroid_mem_affineSpan_face [CharZero k] (s : Affine.Simplex k P n)
    (i : Fin (n + 1)) :
    s.faceOppositeCentroid i ∈ affineSpan k (Set.range (s.faceOpposite i).points) := Affine.Simplex.centroid_mem_affineSpan (s.faceOpposite i)

