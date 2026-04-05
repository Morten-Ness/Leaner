import Mathlib

variable (k : Type*) {V V₂ V₃ : Type*} (P P₂ P₃ : Type*)

variable [Ring k] [AddCommGroup V] [AddCommGroup V₂] [AddCommGroup V₃]

variable [Module k V] [Module k V₂] [Module k V₃]

variable [AddTorsor V P] [AddTorsor V₂ P₂] [AddTorsor V₃ P₃]

variable {P P₂ P₃}

variable {k}

theorem affineSpan_face_le {n : ℕ} (s : Affine.Simplex k P n) {fs : Finset (Fin (n + 1))} {m : ℕ}
    (h : #fs = m + 1) :
    affineSpan k (Set.range (s.face h).points) ≤ affineSpan k (Set.range s.points) := affineSpan_mono k (Affine.Simplex.range_face_points s h ▸ Set.image_subset_range _ _)

