import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [DivisionRing k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {n : ℕ}

theorem affineIndependent_points_update_centroid [CharZero k] (s : Affine.Simplex k P n)
    (i : Fin (n + 1)) :
    AffineIndependent k (Function.update s.points i s.centroid) := by
  have : s.centroid ∉ affineSpan k (s.points '' {i}ᶜ) :=
    Affine.Simplex.centroid_notMem_affineSpan_of_ne_univ s (by simp)
  exact AffineIndependent.affineIndependent_update_of_notMem_affineSpan s.independent this

