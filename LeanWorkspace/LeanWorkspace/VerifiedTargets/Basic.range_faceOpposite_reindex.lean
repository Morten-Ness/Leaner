import Mathlib

variable (k : Type*) {V V₂ V₃ : Type*} (P P₂ P₃ : Type*)

variable [Ring k] [AddCommGroup V] [AddCommGroup V₂] [AddCommGroup V₃]

variable [Module k V] [Module k V₂] [Module k V₃]

variable [AddTorsor V P] [AddTorsor V₂ P₂] [AddTorsor V₃ P₃]

variable {P P₂ P₃}

variable {k}

theorem range_faceOpposite_reindex {m n : ℕ} [NeZero m] [NeZero n] (s : Affine.Simplex k P m)
    (e : Fin (m + 1) ≃ Fin (n + 1)) (i : Fin (n + 1)) :
    Set.range ((s.reindex e).faceOpposite i).points =
      Set.range (s.faceOpposite (e.symm i)).points := by
  rw [Affine.Simplex.faceOpposite, Affine.Simplex.range_face_reindex]
  simp [Equiv.image_compl]

