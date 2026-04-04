import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [DivisionRing k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {n : ℕ}

theorem eq_centroid_iff_sum_vsub_eq_zero [CharZero k] {s : Affine.Simplex k P n} {p : P} :
    p = s.centroid ↔ ∑ i, (s.points i -ᵥ p) = 0 := by
  constructor
  · intro h
    rw [h, Affine.Simplex.centroid_weighted_vsub_eq_zero]
  · intro h
    rw [← vsub_eq_zero_iff_eq]
    have : ∑ i, (s.points i -ᵥ p) = ∑ i, ((s.points i -ᵥ s.centroid) - (p -ᵥ s.centroid)) := by
      apply sum_congr rfl
      intro x hx
      rw [vsub_sub_vsub_cancel_right _ _ s.centroid]
    rw [this, sum_sub_distrib, Affine.Simplex.centroid_weighted_vsub_eq_zero] at h
    simp only [sum_const, card_univ, Fintype.card_fin, zero_sub, neg_eq_zero] at h
    have h' : ((n : k) + 1) • (p -ᵥ s.centroid) = 0 := by norm_cast
    rw [smul_eq_zero_iff_right (by norm_cast)] at h'
    exact h'

