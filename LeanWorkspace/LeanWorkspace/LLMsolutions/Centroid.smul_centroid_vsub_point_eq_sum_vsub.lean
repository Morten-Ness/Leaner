FAIL
import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [DivisionRing k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {n : ℕ}

theorem smul_centroid_vsub_point_eq_sum_vsub [CharZero k] (s : Affine.Simplex k P n)
    (i : Fin (n + 1)) :
    ((n : k) + 1) • (s.centroid -ᵥ s.points i) = ∑ x, (s.points x -ᵥ s.points i) := by
  classical
  rw [Affine.Simplex.centroid_eq_affineCombination]
  simp only [AffineCombination.apply_eq_smul_vsub_add_affineCombinationCoeffs_vadd,
    Affine.Simplex.centroidWeights, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, Nat.smul_vsub_assoc, Nat.cast_add, Nat.cast_one]
  rw [inv_smul_eq_iff₀]
  · simp [smul_sum]
  · exact by positivity
