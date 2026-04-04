import Mathlib

variable (k : Type*) {V V₂ V₃ : Type*} (P P₂ P₃ : Type*)

variable [Ring k] [AddCommGroup V] [AddCommGroup V₂] [AddCommGroup V₃]

variable [Module k V] [Module k V₂] [Module k V₃]

variable [AddTorsor V P] [AddTorsor V₂ P₂] [AddTorsor V₃ P₃]

variable {P P₂ P₃}

variable {k}

theorem restrict_map_subtype {n : ℕ} (s : Affine.Simplex k P n) :
    (s.restrict _ le_rfl).map (AffineSubspace.subtype _) Subtype.coe_injective = s := rfl

