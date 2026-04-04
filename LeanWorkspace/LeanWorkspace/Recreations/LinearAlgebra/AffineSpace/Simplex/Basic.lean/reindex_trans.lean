import Mathlib

variable (k : Type*) {V V₂ V₃ : Type*} (P P₂ P₃ : Type*)

variable [Ring k] [AddCommGroup V] [AddCommGroup V₂] [AddCommGroup V₃]

variable [Module k V] [Module k V₂] [Module k V₃]

variable [AddTorsor V P] [AddTorsor V₂ P₂] [AddTorsor V₃ P₃]

variable {P P₂ P₃}

variable {k}

theorem reindex_trans {n₁ n₂ n₃ : ℕ} (e₁₂ : Fin (n₁ + 1) ≃ Fin (n₂ + 1))
    (e₂₃ : Fin (n₂ + 1) ≃ Fin (n₃ + 1)) (s : Affine.Simplex k P n₁) :
    s.reindex (e₁₂.trans e₂₃) = (s.reindex e₁₂).reindex e₂₃ := rfl

