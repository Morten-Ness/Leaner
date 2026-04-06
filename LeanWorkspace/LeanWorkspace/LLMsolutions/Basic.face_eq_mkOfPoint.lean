FAIL
import Mathlib

variable (k : Type*) {V V₂ V₃ : Type*} (P P₂ P₃ : Type*)

variable [Ring k] [AddCommGroup V] [AddCommGroup V₂] [AddCommGroup V₃]

variable [Module k V] [Module k V₂] [Module k V₃]

variable [AddTorsor V P] [AddTorsor V₂ P₂] [AddTorsor V₃ P₃]

variable {P P₂ P₃}

variable {k}

theorem face_eq_mkOfPoint {n : ℕ} (s : Affine.Simplex k P n) (i : Fin (n + 1)) :
    s.face (Finset.card_singleton i) = Affine.Simplex.mkOfPoint k (s.points i) := by
  ext j
  have h : j = 0 := Subsingleton.elim _ _
  subst h
  simp [Affine.Simplex.face, Affine.Simplex.mkOfPoint]
