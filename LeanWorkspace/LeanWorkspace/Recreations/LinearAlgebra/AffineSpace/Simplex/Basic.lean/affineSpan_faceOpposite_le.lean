import Mathlib

variable (k : Type*) {V V₂ V₃ : Type*} (P P₂ P₃ : Type*)

variable [Ring k] [AddCommGroup V] [AddCommGroup V₂] [AddCommGroup V₃]

variable [Module k V] [Module k V₂] [Module k V₃]

variable [AddTorsor V P] [AddTorsor V₂ P₂] [AddTorsor V₃ P₃]

variable {P P₂ P₃}

variable {k}

theorem affineSpan_faceOpposite_le {n : ℕ} [NeZero n] (s : Affine.Simplex k P n) (i : Fin (n + 1)) :
    affineSpan k (Set.range (s.faceOpposite i).points) ≤ affineSpan k (Set.range s.points) := s.affineSpan_face_le _

