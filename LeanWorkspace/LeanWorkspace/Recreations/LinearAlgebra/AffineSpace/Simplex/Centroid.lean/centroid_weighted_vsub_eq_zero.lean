import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [DivisionRing k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {n : ℕ}

theorem centroid_weighted_vsub_eq_zero [CharZero k] (s : Affine.Simplex k P n) :
    ∑ i, (s.points i -ᵥ s.centroid) = 0 := by
  have h := Affine.Simplex.centroid_vsub_eq s s.centroid
  simp only [vsub_self] at h
  symm at h
  rw [smul_eq_zero_iff_right (inv_ne_zero (by norm_cast))] at h
  exact h

