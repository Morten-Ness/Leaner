import Mathlib

variable (k : Type*) {V V₂ V₃ : Type*} (P P₂ P₃ : Type*)

variable [Ring k] [AddCommGroup V] [AddCommGroup V₂] [AddCommGroup V₃]

variable [Module k V] [Module k V₂] [Module k V₃]

variable [AddTorsor V P] [AddTorsor V₂ P₂] [AddTorsor V₃ P₃]

variable {P P₂ P₃}

variable {k}

theorem faceOpposite_point_eq_point_rev (s : Affine.Simplex k P 1) (i : Fin 2) (n : Fin 1) :
    (s.faceOpposite i).points n = s.points i.rev := by
  have h : i.rev = Fin.succAbove i n := by decide +revert
  simp [h, Affine.Simplex.faceOpposite_point_eq_point_succAbove]

