import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [DivisionRing k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {n : ℕ}

theorem face_centroid_eq_centroid {n : ℕ} (s : Affine.Simplex k P n) {fs : Finset (Fin (n + 1))} {m : ℕ}
    (h : #fs = m + 1) : Finset.univ.centroid k (s.face h).points = fs.centroid k s.points := by
  convert (Finset.univ.centroid_map k (fs.orderEmbOfFin h).toEmbedding s.points).symm
  rw [← Finset.coe_inj, Finset.coe_map, Finset.coe_univ, Set.image_univ]
  simp

