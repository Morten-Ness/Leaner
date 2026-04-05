import Mathlib

variable (k : Type*) {V V₂ V₃ : Type*} (P P₂ P₃ : Type*)

variable [Ring k] [AddCommGroup V] [AddCommGroup V₂] [AddCommGroup V₃]

variable [Module k V] [Module k V₂] [Module k V₃]

variable [AddTorsor V P] [AddTorsor V₂ P₂] [AddTorsor V₃ P₃]

variable {P P₂ P₃}

variable {k}

theorem reindex_symm_reindex {m n : ℕ} (s : Affine.Simplex k P m) (e : Fin (n + 1) ≃ Fin (m + 1)) :
    (s.reindex e.symm).reindex e = s := by rw [← Affine.Simplex.reindex_trans, Equiv.symm_trans_self, Affine.Simplex.reindex_refl]

