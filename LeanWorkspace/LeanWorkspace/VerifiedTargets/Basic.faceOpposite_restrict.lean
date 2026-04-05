import Mathlib

variable (k : Type*) {V V₂ V₃ : Type*} (P P₂ P₃ : Type*)

variable [Ring k] [AddCommGroup V] [AddCommGroup V₂] [AddCommGroup V₃]

variable [Module k V] [Module k V₂] [Module k V₃]

variable [AddTorsor V P] [AddTorsor V₂ P₂] [AddTorsor V₃ P₃]

variable {P P₂ P₃}

variable {k}

theorem faceOpposite_restrict {n : ℕ} [NeZero n] (s : Affine.Simplex k P n) {S : AffineSubspace k P}
    (hS : affineSpan k (Set.range s.points) ≤ S) (i : Fin (n + 1)) :
    letI := Nonempty.map (AffineSubspace.inclusion hS) inferInstance
    (s.restrict S hS).faceOpposite i = (s.faceOpposite i).restrict S
      ((Affine.Simplex.affineSpan_faceOpposite_le s i).trans hS) :=
  Affine.Simplex.face_restrict s hS _

