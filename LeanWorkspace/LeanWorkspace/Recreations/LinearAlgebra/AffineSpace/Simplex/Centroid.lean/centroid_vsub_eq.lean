import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [DivisionRing k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {n : ℕ}

theorem centroid_vsub_eq {n : ℕ} [CharZero k] (s : Affine.Simplex k P n) (p : P) :
    s.centroid -ᵥ p = (n + 1 : k)⁻¹ • ∑ x, (s.points x -ᵥ p) := by
  rw [centroid_vsub_const _ _ (by simp), centroid_def, affineCombination_eq_linear_combination
    (hw := sum_centroidWeights_eq_one_of_nonempty _ _ (by simp))]
  simp [smul_sum]

