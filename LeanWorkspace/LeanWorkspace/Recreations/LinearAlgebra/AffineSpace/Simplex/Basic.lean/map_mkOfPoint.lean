import Mathlib

variable (k : Type*) {V V₂ V₃ : Type*} (P P₂ P₃ : Type*)

variable [Ring k] [AddCommGroup V] [AddCommGroup V₂] [AddCommGroup V₃]

variable [Module k V] [Module k V₂] [Module k V₃]

variable [AddTorsor V P] [AddTorsor V₂ P₂] [AddTorsor V₃ P₃]

variable {P P₂ P₃}

variable {k}

theorem map_mkOfPoint (f : P →ᵃ[k] P₂) (hf : Function.Injective f) (p : P) :
    (Affine.Simplex.mkOfPoint k p).map f hf = Affine.Simplex.mkOfPoint k (f p) := rfl

