import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [DivisionRing k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {n : ℕ}

theorem centroid_map [CharZero k] {V₂ P₂ : Type*} [AddCommGroup V₂] [Module k V₂]
    [AddTorsor V₂ P₂] {n : ℕ} (s : Affine.Simplex k P n) (f : P →ᵃ[k] P₂)
    (hf : Function.Injective f) :
    (s.map f hf).centroid = f (s.centroid) := by
  rw [centroid, map_points, Affine.Simplex.centroid_eq_affineCombination, Finset.map_affineCombination]
  · rw [Finset.centroid]
  · rw [sum_centroidWeights_eq_one_of_card_ne_zero]
    simp

