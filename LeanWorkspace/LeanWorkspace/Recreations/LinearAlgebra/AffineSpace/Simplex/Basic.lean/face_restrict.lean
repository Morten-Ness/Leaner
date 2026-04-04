import Mathlib

variable (k : Type*) {V V₂ V₃ : Type*} (P P₂ P₃ : Type*)

variable [Ring k] [AddCommGroup V] [AddCommGroup V₂] [AddCommGroup V₃]

variable [Module k V] [Module k V₂] [Module k V₃]

variable [AddTorsor V P] [AddTorsor V₂ P₂] [AddTorsor V₃ P₃]

variable {P P₂ P₃}

variable {k}

theorem face_restrict {n : ℕ} (s : Affine.Simplex k P n) {S : AffineSubspace k P}
    (hS : affineSpan k (Set.range s.points) ≤ S) {fs : Finset (Fin (n + 1))} {m : ℕ}
    (h : #fs = m + 1) :
    letI := Nonempty.map (AffineSubspace.inclusion hS) inferInstance
    (s.restrict S hS).face h = (s.face h).restrict S ((s.affineSpan_face_le h).trans hS) := by
  letI := Nonempty.map (AffineSubspace.inclusion hS) inferInstance
  Affine.Simplex.ext i
  rw [restrict_points_coe]
  simp_rw [Affine.Simplex.face_points]
  simp

