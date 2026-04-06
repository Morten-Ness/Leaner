FAIL
import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [DivisionRing k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {n : ℕ}

theorem centroid_weighted_vsub_eq_zero [CharZero k] (s : Affine.Simplex k P n) :
    ∑ i, (s.points i -ᵥ s.centroid) = 0 := by
  classical
  rw [Affine.Simplex.centroid]
  let w : Fin (n + 1) → k := fun _ => ((n + 1 : ℕ) : k)⁻¹
  have hw : Finset.univ.sum w = (1 : k) := by
    simp [w]
  simpa [w] using AffineMap.weightedVSub_vadd_eq_weightedVSubOfPoint_vadd hw s.points s.points 0
