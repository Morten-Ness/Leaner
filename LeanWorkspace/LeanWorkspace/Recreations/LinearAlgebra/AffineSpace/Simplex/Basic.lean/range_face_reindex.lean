import Mathlib

variable (k : Type*) {V V₂ V₃ : Type*} (P P₂ P₃ : Type*)

variable [Ring k] [AddCommGroup V] [AddCommGroup V₂] [AddCommGroup V₃]

variable [Module k V] [Module k V₂] [Module k V₃]

variable [AddTorsor V P] [AddTorsor V₂ P₂] [AddTorsor V₃ P₃]

variable {P P₂ P₃}

variable {k}

theorem range_face_reindex {m n : ℕ} (s : Affine.Simplex k P m) (e : Fin (m + 1) ≃ Fin (n + 1))
    {fs : Finset (Fin (n + 1))} {n' : ℕ} (h : #fs = n' + 1) :
    Set.range ((s.reindex e).face h).points =
      Set.range (s.face (fs := fs.map e.symm.toEmbedding) (h ▸ Finset.card_map _)).points := by
  simp only [Affine.Simplex.range_face_points, reindex_points, Set.image_comp]
  simp

